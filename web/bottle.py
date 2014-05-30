#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""
Bottle is a fast and simple micro-framework for small web applications. It
offers request dispatching (Routes) with url parameter support, templates,
a built-in HTTP Server and adapters for many third party WSGI/HTTP-server and
template engines - all in a single file and with no dependencies other than the
Python Standard Library.

Homepage and documentation: http://bottlepy.org/

Copyright (c) 2014, Marcel Hellkamp.
License: MIT (see LICENSE for details)
"""

from __future__ import with_statement

__author__ = 'Marcel Hellkamp'
__version__ = '0.13-dev'
__license__ = 'MIT'

# The gevent server adapter needs to patch some modules before they are imported
# This is why we parse the commandline parameters here but handle them later
if __name__ == '__main__':
    from optparse import OptionParser
    _cmd_parser = OptionParser(usage="usage: %prog [options] package.module:app")
    _opt = _cmd_parser.add_option
    _opt("--version", action="store_true", help="show version number.")
    _opt("-b", "--bind", metavar="ADDRESS", help="bind socket to ADDRESS.")
    _opt("-s", "--server", default='wsgiref', help="use SERVER as backend.")
    _opt("-p", "--plugin", action="append", help="install additional plugin/s.")
    _opt("--debug", action="store_true", help="start server in debug mode.")
    _opt("--reload", action="store_true", help="auto-reload on file changes.")
    _cmd_options, _cmd_args = _cmd_parser.parse_args()
    if _cmd_options.server and _cmd_options.server.startswith('gevent'):
        import gevent.monkey; gevent.monkey.patch_all()

import base64, cgi, email.utils, functools, hmac, imp, itertools, mimetypes,\
        os, re, subprocess, sys, tempfile, threading, time, warnings

from datetime import date as datedate, datetime, timedelta
from tempfile import TemporaryFile
from traceback import format_exc, print_exc
from inspect import getargspec
from unicodedata import normalize


try: from simplejson import dumps as json_dumps, loads as json_lds
except ImportError: # pragma: no cover
    try: from json import dumps as json_dumps, loads as json_lds
    except ImportError:
        try: from django.utils.simplejson import dumps as json_dumps, loads as json_lds
        except ImportError:
            def json_dumps(data):
                raise ImportError("JSON support requires Python 2.6 or simplejson.")
            json_lds = json_dumps



# We now try to fix 2.5/2.6/3.1/3.2 incompatibilities.
# It ain't pretty but it works... Sorry for the mess.

py   = sys.version_info
py3k = py >= (3, 0, 0)
py25 = py <  (2, 6, 0)
py31 = (3, 1, 0) <= py < (3, 2, 0)

# Workaround for the missing "as" keyword in py3k.
def _e(): return sys.exc_info()[1]

# Workaround for the "print is a keyword/function" Python 2/3 dilemma
# and a fallback for mod_wsgi (resticts stdout/err attribute access)
try:
    _stdout, _stderr = sys.stdout.write, sys.stderr.write
except IOError:
    _stdout = lambda x: sys.stdout.write(x)
    _stderr = lambda x: sys.stderr.write(x)

# Lots of stdlib and builtin differences.
if py3k:
    import http.client as httplib
    import _thread as thread
    from urllib.parse import urljoin, SplitResult as UrlSplitResult
    from urllib.parse import urlencode, quote as urlquote, unquote as urlunquote
    urlunquote = functools.partial(urlunquote, encoding='latin1')
    from http.cookies import SimpleCookie
    from collections import MutableMapping as DictMixin
    import pickle
    from io import BytesIO
    from configparser import ConfigParser
    basestring = str
    unicode = str
    json_loads = lambda s: json_lds(touni(s))
    callable = lambda x: hasattr(x, '__call__')
    imap = map
    def _raise(*a): raise a[0](a[1]).with_traceback(a[2])
else: # 2.x
    import httplib
    import thread
    from urlparse import urljoin, SplitResult as UrlSplitResult
    from urllib import urlencode, quote as urlquote, unquote as urlunquote
    from Cookie import SimpleCookie
    from itertools import imap
    import cPickle as pickle
    from StringIO import StringIO as BytesIO
    from ConfigParser import SafeConfigParser as ConfigParser
    if py25:
        msg  = "Python 2.5 support may be dropped in future versions of Bottle."
        warnings.warn(msg, DeprecationWarning)
        from UserDict import DictMixin
        def next(it): return it.next()
        bytes = str
    else: # 2.6, 2.7
        from collections import MutableMapping as DictMixin
    unicode = unicode
    json_loads = json_lds
    eval(compile('def _raise(*a): raise a[0], a[1], a[2]', '<py3fix>', 'exec'))

# Some helpers for string/byte handling
def tob(s, enc='utf8'):
    return s.encode(enc) if isinstance(s, unicode) else bytes(s)

def touni(s, enc='utf8', err='strict'):
    if isinstance(s, bytes):
        return s.decode(enc, err)
    else:
        return unicode(s or ("" if s is None else s))

tonat = touni if py3k else tob

# 3.2 fixes cgi.FieldStorage to accept bytes (which makes a lot of sense).
# 3.1 needs a workaround.
if py31:
    from io import TextIOWrapper
    class NCTextIOWrapper(TextIOWrapper):
        def close(self): pass # Keep wrapped buffer open.


# A bug in functools causes it to break if the wrapper is an instance method
def update_wrapper(wrapper, wrapped, *a, **ka):
    try: functools.update_wrapper(wrapper, wrapped, *a, **ka)
    except AttributeError: pass



# These helpers are used at module level and need to be defined first.
# And yes, I know PEP-8, but sometimes a lower-case classname makes more sense.

def depr(message, hard=False):
    warnings.warn(message, DeprecationWarning, stacklevel=3)

def makelist(data): # This is just to handy
    if isinstance(data, (tuple, list, set, dict)): return list(data)
    elif data: return [data]
    else: return []


class DictProperty(object):
    ''' Property that maps to a key in a local dict-like attribute. '''
    def __init__(self, attr, key=None, read_only=False):
        self.attr, self.key, self.read_only = attr, key, read_only

    def __call__(self, func):
        functools.update_wrapper(self, func, updated=[])
        self.getter, self.key = func, self.key or func.__name__
        return self

    def __get__(self, obj, cls):
        if obj is None: return self
        key, storage = self.key, getattr(obj, self.attr)
        if key not in storage: storage[key] = self.getter(obj)
        return storage[key]

    def __set__(self, obj, value):
        if self.read_only: raise AttributeError("Read-Only property.")
        getattr(obj, self.attr)[self.key] = value

    def __delete__(self, obj):
        if self.read_only: raise AttributeError("Read-Only property.")
        del getattr(obj, self.attr)[self.key]


class cached_property(object):
    ''' A property that is only computed once per instance and then replaces
        itself with an ordinary attribute. Deleting the attribute resets the
        property. '''

    def __init__(self, func):
        self.__doc__ = getattr(func, '__doc__')
        self.func = func

    def __get__(self, obj, cls):
        if obj is None: return self
        value = obj.__dict__[self.func.__name__] = self.func(obj)
        return value


class lazy_attribute(object):
    ''' A property that caches itself to the class object. '''
    def __init__(self, func):
        functools.update_wrapper(self, func, updated=[])
        self.getter = func

    def __get__(self, obj, cls):
        value = self.getter(cls)
        setattr(cls, self.__name__, value)
        return value






###############################################################################
# Exceptions and Events ########################################################
###############################################################################


class BottleException(Exception):
    """ A base class for exceptions used by bottle. """
    pass






###############################################################################
# Routing ######################################################################
###############################################################################


class RouteError(BottleException):
    """ This is a base class for all routing related exceptions """


class RouteReset(BottleException):
    """ If raised by a plugin or request handler, the route is reset and all
        plugins are re-applied. """

class RouterUnknownModeError(RouteError): pass


class RouteSyntaxError(RouteError):
    """ The route parser found something not supported by this router. """


class RouteBuildError(RouteError):
    """ The route could not be built. """


def _re_flatten(p):
    ''' Turn all capturing groups in a regular expression pattern into
        non-capturing groups. '''
    if '(' not in p: return p
    return re.sub(r'(\\*)(\(\?P<[^>]+>|\((?!\?))',
        lambda m: m.group(0) if len(m.group(1)) % 2 else m.group(1) + '(?:', p)


class Router(object):
    ''' A Router is an ordered collection of route->target pairs. It is used to
        efficiently match WSGI requests against a number of routes and return
        the first target that satisfies the request. The target may be anything,
        usually a string, ID or callable object. A route consists of a path-rule
        and a HTTP method.

        The path-rule is either a static path (e.g. `/contact`) or a dynamic
        path that contains wildcards (e.g. `/wiki/<page>`). The wildcard syntax
        and details on the matching order are described in docs:`routing`.
    '''

    default_pattern = '[^/]+'
    default_filter  = 're'

    #: The current CPython regexp implementation does not allow more
    #: than 99 matching groups per regular expression.
    _MAX_GROUPS_PER_PATTERN = 99

    def __init__(self, strict=False):
        self.rules    = [] # All rules in order
        self._groups  = {} # index of regexes to find them in dyna_routes
        self.builder  = {} # Data structure for the url builder
        self.static   = {} # Search structure for static routes
        self.dyna_routes   = {}
        self.dyna_regexes  = {} # Search structure for dynamic routes
        #: If true, static routes are no longer checked first.
        self.strict_order = strict
        self.filters = {
            're':    lambda conf:
                (_re_flatten(conf or self.default_pattern), None, None),
            'int':   lambda conf: (r'-?\d+', int, lambda x: str(int(x))),
            'float': lambda conf: (r'-?[\d.]+', float, lambda x: str(float(x))),
            'path':  lambda conf: (r'.+?', None, None)}

    def add_filter(self, name, func):
        ''' Add a filter. The provided function is called with the configuration
        string as parameter and must return a (regexp, to_python, to_url) tuple.
        The first element is a string, the last two are callables or None. '''
        self.filters[name] = func

    rule_syntax = re.compile('(\\\\*)'\
        '(?:(?::([a-zA-Z_][a-zA-Z_0-9]*)?()(?:#(.*?)#)?)'\
          '|(?:<([a-zA-Z_][a-zA-Z_0-9]*)?(?::([a-zA-Z_]*)'\
            '(?::((?:\\\\.|[^\\\\>]+)+)?)?)?>))')

    def _itertokens(self, rule):
        offset, prefix = 0, ''
        for match in self.rule_syntax.finditer(rule):
            prefix += rule[offset:match.start()]
            g = match.groups()
            if len(g[0])%2: # Escaped wildcard
                prefix += match.group(0)[len(g[0]):]
                offset = match.end()
                continue
            if prefix:
                yield prefix, None, None
            name, filtr, conf = g[4:7] if g[2] is None else g[1:4]
            yield name, filtr or 'default', conf or None
            offset, prefix = match.end(), ''
        if offset <= len(rule) or prefix:
            yield prefix+rule[offset:], None, None

    def add(self, rule, method, target, name=None):
        ''' Add a new rule or replace the target for an existing rule. '''
        anons     = 0    # Number of anonymous wildcards found
        keys      = []   # Names of keys
        pattern   = ''   # Regular expression pattern with named groups
        filters   = []   # Lists of wildcard input filters
        builder   = []   # Data structure for the URL builder
        is_static = True

        for key, mode, conf in self._itertokens(rule):
            if mode:
                is_static = False
                if mode == 'default': mode = self.default_filter
                mask, in_filter, out_filter = self.filters[mode](conf)
                if not key:
                    pattern += '(?:%s)' % mask
                    key = 'anon%d' % anons
                    anons += 1
                else:
                    pattern += '(?P<%s>%s)' % (key, mask)
                    keys.append(key)
                if in_filter: filters.append((key, in_filter))
                builder.append((key, out_filter or str))
            elif key:
                pattern += re.escape(key)
                builder.append((None, key))

        self.builder[rule] = builder
        if name: self.builder[name] = builder

        if is_static and not self.strict_order:
            self.static.setdefault(method, {})
            self.static[method][self.build(rule)] = (target, None)
            return

        try:
            re_pattern = re.compile('^(%s)$' % pattern)
            re_match = re_pattern.match
        except re.error:
            raise RouteSyntaxError("Could not add Route: %s (%s)" % (rule, _e()))

        if filters:
            def getargs(path):
                url_args = re_match(path).groupdict()
                for name, wildcard_filter in filters:
                    try:
                        url_args[name] = wildcard_filter(url_args[name])
                    except ValueError:
                        raise HTTPError(400, 'Path has wrong format.')
                return url_args
        elif re_pattern.groupindex:
            def getargs(path):
                return re_match(path).groupdict()
        else:
            getargs = None

        flatpat = _re_flatten(pattern)
        whole_rule = (rule, flatpat, target, getargs)

        if (flatpat, method) in self._groups:
            if DEBUG:
                msg = 'Route <%s %s> overwrites a previously defined route'
                warnings.warn(msg % (method, rule), RuntimeWarning)
            self.dyna_routes[method][self._groups[flatpat, method]] = whole_rule
        else:
            self.dyna_routes.setdefault(method, []).append(whole_rule)
            self._groups[flatpat, method] = len(self.dyna_routes[method]) - 1

        self._compile(method)

    def _compile(self, method):
        all_rules = self.dyna_routes[method]
        comborules = self.dyna_regexes[method] = []
        maxgroups = self._MAX_GROUPS_PER_PATTERN
        for x in range(0, len(all_rules), maxgroups):
            some = all_rules[x:x+maxgroups]
            combined = (flatpat for (_, flatpat, _, _) in some)
            combined = '|'.join('(^%s$)' % flatpat for flatpat in combined)
            combined = re.compile(combined).match
            rules = [(target, getargs) for (_, _, target, getargs) in some]
            comborules.append((combined, rules))

    def build(self, _name, *anons, **query):
        ''' Build an URL by filling the wildcards in a rule. '''
        builder = self.builder.get(_name)
        if not builder: raise RouteBuildError("No route with that name.", _name)
        try:
            for i, value in enumerate(anons): query['anon%d'%i] = value
            url = ''.join([f(query.pop(n)) if n else f for (n,f) in builder])
            return url if not query else url+'?'+urlencode(query)
        except KeyError:
            raise RouteBuildError('Missing URL argument: %r' % _e().args[0])

    def match(self, environ):
        ''' Return a (target, url_agrs) tuple or raise HTTPError(400/404/405). '''
        verb = environ['REQUEST_METHOD'].upper()
        path = environ['PATH_INFO'] or '/'
        target = None
        if verb == 'HEAD':
            methods = ['PROXY', verb, 'GET', 'ANY']
        else:
            methods = ['PROXY', verb, 'ANY']

        for method in methods:
            if method in self.static and path in self.static[method]:
                target, getargs = self.static[method][path]
                return target, getargs(path) if getargs else {}
            elif method in self.dyna_regexes:
                for combined, rules in self.dyna_regexes[method]:
                    match = combined(path)
                    if match:
                        target, getargs = rules[match.lastindex - 1]
                        return target, getargs(path) if getargs else {}

        # No matching route found. Collect alternative methods for 405 response
        allowed = set([])
        nocheck = set(methods)
        for method in set(self.static) - nocheck:
            if path in self.static[method]:
                allowed.add(verb)
        for method in set(self.dyna_regexes) - allowed - nocheck:
            for combined, rules in self.dyna_regexes[method]:
                match = combined(path)
                if match:
                    allowed.add(method)
        if allowed:
            allow_header = ",".join(sorted(allowed))
            raise HTTPError(405, "Method not allowed.", Allow=allow_header)

        # No matching route and no alternative method found. We give up
        raise HTTPError(404, "Not found: " + repr(path))






class Route(object):
    ''' This class wraps a route callback along with route specific metadata and
        configuration and applies Plugins on demand. It is also responsible for
        turing an URL path rule into a regular expression usable by the Router.
    '''

    def __init__(self, app, rule, method, callback, name=None,
                 plugins=None, skiplist=None, **config):
        #: The application this route is installed to.
        self.app = app
        #: The path-rule string (e.g. ``/wiki/:page``).
        self.rule = rule
        #: The HTTP method as a string (e.g. ``GET``).
        self.method = method
        #: The original callback with no plugins applied. Useful for introspection.
        self.callback = callback
        #: The name of the route (if specified) or ``None``.
        self.name = name or None
        #: A list of route-specific plugins (see :meth:`Bottle.route`).
        self.plugins = plugins or []
        #: A list of plugins to not apply to this route (see :meth:`Bottle.route`).
        self.skiplist = skiplist or []
        #: Additional keyword arguments passed to the :meth:`Bottle.route`
        #: decorator are stored in this dictionary. Used for route-specific
        #: plugin configuration and meta-data.
        self.config = ConfigDict().load_dict(config)

    @cached_property
    def call(self):
        ''' The route callback with all plugins applied. This property is
            created on demand and then cached to speed up subsequent requests.'''
        return self._make_callback()

    def reset(self):
        ''' Forget any cached values. The next time :attr:`call` is accessed,
            all plugins are re-applied. '''
        self.__dict__.pop('call', None)

    def prepare(self):
        ''' Do all on-demand work immediately (useful for debugging).'''
        self.call

    def all_plugins(self):
        ''' Yield all Plugins affecting this route. '''
        unique = set()
        for p in reversed(self.app.plugins + self.plugins):
            if True in self.skiplist: break
            name = getattr(p, 'name', False)
            if name and (name in self.skiplist or name in unique): continue
            if p in self.skiplist or type(p) in self.skiplist: continue
            if name: unique.add(name)
            yield p

    def _make_callback(self):
        callback = self.callback
        for plugin in self.all_plugins():
            try:
                if hasattr(plugin, 'apply'):
                    callback = plugin.apply(callback, self)
                else:
                    callback = plugin(callback)
            except RouteReset: # Try again with changed configuration.
                return self._make_callback()
            if not callback is self.callback:
                update_wrapper(callback, self.callback)
        return callback

    def get_undecorated_callback(self):
        ''' Return the callback. If the callback is a decorated function, try to
            recover the original function. '''
        func = self.callback
        func = getattr(func, '__func__' if py3k else 'im_func', func)
        closure_attr = '__closure__' if py3k else 'func_closure'
        while hasattr(func, closure_attr) and getattr(func, closure_attr):
            func = getattr(func, closure_attr)[0].cell_contents
        return func

    def get_callback_args(self):
        ''' Return a list of argument names the callback (most likely) accepts
            as keyword arguments. If the callback is a decorated function, try
            to recover the original function before inspection. '''
        return getargspec(self.get_undecorated_callback())[0]

    def get_config(self, key, default=None):
        ''' Lookup a config field and return its value, first checking the
            route.config, then route.app.config.'''
        for conf in (self.config, self.app.conifg):
            if key in conf: return conf[key]
        return default

    def __repr__(self):
        cb = self.get_undecorated_callback()
        return '<%s %r %r>' % (self.method, self.rule, cb)






###############################################################################
# Application Object ###########################################################
###############################################################################


class Bottle(object):
    """ Each Bottle object represents a single, distinct web application and
        consists of routes, callbacks, plugins, resources and configuration.
        Instances are callable WSGI applications.

        :param catchall: If true (default), handle all exceptions. Turn off to
                         let debugging middleware handle exceptions.
    """

    def __init__(self, catchall=True, autojson=True):

        #: A :class:`ConfigDict` for app specific configuration.
        self.config = ConfigDict()
        self.config._on_change = functools.partial(self.trigger_hook, 'config')
        self.config.meta_set('autojson', 'validate', bool)
        self.config.meta_set('catchall', 'validate', bool)
        self.config['catchall'] = catchall
        self.config['autojson'] = autojson

        #: A :class:`ResourceManager` for application files
        self.resources = ResourceManager()

        self.routes = [] # List of installed :class:`Route` instances.
        self.router = Router() # Maps requests to :class:`Route` instances.
        self.error_handler = {}

        # Core plugins
        self.plugins = [] # List of installed plugins.
        if self.config['autojson']:
            self.install(JSONPlugin())
        self.install(TemplatePlugin())

    #: If true, most exceptions are caught and returned as :exc:`HTTPError`
    catchall = DictProperty('config', 'catchall')

    __hook_names = 'before_request', 'after_request', 'app_reset', 'config'
    __hook_reversed = 'after_request'

    @cached_property
    def _hooks(self):
        return dict((name, []) for name in self.__hook_names)

    def add_hook(self, name, func):
        ''' Attach a callback to a hook. Three hooks are currently implemented:

            before_request
                Executed once before each request. The request context is
                available, but no routing has happened yet.
            after_request
                Executed once after each request regardless of its outcome.
            app_reset
                Called whenever :meth:`Bottle.reset` is called.
        '''
        if name in self.__hook_reversed:
            self._hooks[name].insert(0, func)
        else:
            self._hooks[name].append(func)

    def remove_hook(self, name, func):
        ''' Remove a callback from a hook. '''
        if name in self._hooks and func in self._hooks[name]:
            self._hooks[name].remove(func)
            return True

    def trigger_hook(self, __name, *args, **kwargs):
        ''' Trigger a hook and return a list of results. '''
        return [hook(*args, **kwargs) for hook in self._hooks[__name][:]]

    def hook(self, name):
        """ Return a decorator that attaches a callback to a hook. See
            :meth:`add_hook` for details."""
        def decorator(func):
            self.add_hook(name, func)
            return func
        return decorator

    def mount(self, prefix, app, **options):
        ''' Mount an application (:class:`Bottle` or plain WSGI) to a specific
            URL prefix. Example::

                root_app.mount('/admin/', admin_app)

            :param prefix: path prefix or `mount-point`. If it ends in a slash,
                that slash is mandatory.
            :param app: an instance of :class:`Bottle` or a WSGI application.

            All other parameters are passed to the underlying :meth:`route` call.
        '''

        segments = [p for p in prefix.split('/') if p]
        if not segments: raise ValueError('Empty path prefix.')
        path_depth = len(segments)

        def mountpoint_wrapper():
            try:
                request.path_shift(path_depth)
                rs = HTTPResponse([])
                def start_response(status, headerlist, exc_info=None):
                    if exc_info:
                        try:
                            _raise(*exc_info)
                        finally:
                            exc_info = None
                    rs.status = status
                    for name, value in headerlist: rs.add_header(name, value)
                    return rs.body.append
                body = app(request.environ, start_response)
                if body and rs.body: body = itertools.chain(rs.body, body)
                rs.body = body or rs.body
                return rs
            finally:
                request.path_shift(-path_depth)

        options.setdefault('skip', True)
        options.setdefault('method', 'PROXY')
        options.setdefault('mountpoint', {'prefix': prefix, 'target': app})
        options['callback'] = mountpoint_wrapper

        self.route('/%s/<:re:.*>' % '/'.join(segments), **options)
        if not prefix.endswith('/'):
            self.route('/' + '/'.join(segments), **options)

    def merge(self, routes):
        ''' Merge the routes of another :class:`Bottle` application or a list of
            :class:`Route` objects into this application. The routes keep their
            'owner', meaning that the :data:`Route.app` attribute is not
            changed. '''
        if isinstance(routes, Bottle):
            routes = routes.routes
        for route in routes:
            self.add_route(route)

    def install(self, plugin):
        ''' Add a plugin to the list of plugins and prepare it for being
            applied to all routes of this application. A plugin may be a simple
            decorator or an object that implements the :class:`Plugin` API.
        '''
        if hasattr(plugin, 'setup'): plugin.setup(self)
        if not callable(plugin) and not hasattr(plugin, 'apply'):
            raise TypeError("Plugins must be callable or implement .apply()")
        self.plugins.append(plugin)
        self.reset()
        return plugin

    def uninstall(self, plugin):
        ''' Uninstall plugins. Pass an instance to remove a specific plugin, a type
            object to remove all plugins that match that type, a string to remove
            all plugins with a matching ``name`` attribute or ``True`` to remove all
            plugins. Return the list of removed plugins. '''
        removed, remove = [], plugin
        for i, plugin in list(enumerate(self.plugins))[::-1]:
            if remove is True or remove is plugin or remove is type(plugin) \
            or getattr(plugin, 'name', True) == remove:
                removed.append(plugin)
                del self.plugins[i]
                if hasattr(plugin, 'close'): plugin.close()
        if removed: self.reset()
        return removed

    def reset(self, route=None):
        ''' Reset all routes (force plugins to be re-applied) and clear all
            caches. If an ID or route object is given, only that specific route
            is affected. '''
        if route is None: routes = self.routes
        elif isinstance(route, Route): routes = [route]
        else: routes = [self.routes[route]]
        for route in routes: route.reset()
        if DEBUG:
            for route in routes: route.prepare()
        self.trigger_hook('app_reset')

    def close(self):
        ''' Close the application and all installed plugins. '''
        for plugin in self.plugins:
            if hasattr(plugin, 'close'): plugin.close()
        self.stopped = True

    def run(self, **kwargs):
        ''' Calls :func:`run` with the same parameters. '''
        run(self, **kwargs)

    def match(self, environ):
        """ Search for a matching route and return a (:class:`Route` , urlargs)
            tuple. The second value is a dictionary with parameters extracted
            from the URL. Raise :exc:`HTTPError` (404/405) on a non-match."""
        return self.router.match(environ)

    def get_url(self, routename, **kargs):
        """ Return a string that matches a named route """
        scriptname = request.environ.get('SCRIPT_NAME', '').strip('/') + '/'
        location = self.router.build(routename, **kargs).lstrip('/')
        return urljoin(urljoin('/', scriptname), location)

    def add_route(self, route):
        ''' Add a route object, but do not change the :data:`Route.app`
            attribute.'''
        self.routes.append(route)
        self.router.add(route.rule, route.method, route, name=route.name)
        if DEBUG: route.prepare()

    def route(self, path=None, method='GET', callback=None, name=None,
              apply=None, skip=None, **config):
        """ A decorator to bind a function to a request URL. Example::

                @app.route('/hello/:name')
                def hello(name):
                    return 'Hello %s' % name

            The ``:name`` part is a wildcard. See :class:`Router` for syntax
            details.

            :param path: Request path or a list of paths to listen to. If no
              path is specified, it is automatically generated from the
              signature of the function.
            :param method: HTTP method (`GET`, `POST`, `PUT`, ...) or a list of
              methods to listen to. (default: `GET`)
            :param callback: An optional shortcut to avoid the decorator
              syntax. ``route(..., callback=func)`` equals ``route(...)(func)``
            :param name: The name for this route. (default: None)
            :param apply: A decorator or plugin or a list of plugins. These are
              applied to the route callback in addition to installed plugins.
            :param skip: A list of plugins, plugin classes or names. Matching
              plugins are not installed to this route. ``True`` skips all.

            Any additional keyword arguments are stored as route-specific
            configuration and passed to plugins (see :meth:`Plugin.apply`).
        """
        if callable(path): path, callback = None, path
        plugins = makelist(apply)
        skiplist = makelist(skip)
        def decorator(callback):
            # TODO: Documentation and tests
            if isinstance(callback, basestring): callback = load(callback)
            for rule in makelist(path) or yieldroutes(callback):
                for verb in makelist(method):
                    verb = verb.upper()
                    route = Route(self, rule, verb, callback, name=name,
                                  plugins=plugins, skiplist=skiplist, **config)
                    self.add_route(route)
            return callback
        return decorator(callback) if callback else decorator

    def get(self, path=None, method='GET', **options):
        """ Equals :meth:`route`. """
        return self.route(path, method, **options)

    def post(self, path=None, method='POST', **options):
        """ Equals :meth:`route` with a ``POST`` method parameter. """
        return self.route(path, method, **options)

    def put(self, path=None, method='PUT', **options):
        """ Equals :meth:`route` with a ``PUT`` method parameter. """
        return self.route(path, method, **options)

    def delete(self, path=None, method='DELETE', **options):
        """ Equals :meth:`route` with a ``DELETE`` method parameter. """
        return self.route(path, method, **options)

    def error(self, code=500):
        """ Decorator: Register an output handler for a HTTP error code"""
        def wrapper(handler):
            self.error_handler[int(code)] = handler
            return handler
        return wrapper

    def default_error_handler(self, res):
        return tob(template(ERROR_PAGE_TEMPLATE, e=res))

    def _handle(self, environ):
        path = environ['bottle.raw_path'] = environ['PATH_INFO']
        if py3k:
            try:
                environ['PATH_INFO'] = path.encode('latin1').decode('utf8')
            except UnicodeError:
                return HTTPError(400, 'Invalid path string. Expected UTF-8')

        try:
            environ['bottle.app'] = self
            request.bind(environ)
            response.bind()
            try:
                self.trigger_hook('before_request')
                route, args = self.router.match(environ)
                environ['route.handle'] = route
                environ['bottle.route'] = route
                environ['route.url_args'] = args
                return route.call(**args)
            finally:
                self.trigger_hook('after_request')

        except HTTPResponse:
            return _e()
        except RouteReset:
            route.reset()
            return self._handle(environ)
        except (KeyboardInterrupt, SystemExit, MemoryError):
            raise
        except Exception:
            if not self.catchall: raise
            stacktrace = format_exc()
            environ['wsgi.errors'].write(stacktrace)
            return HTTPError(500, "Internal Server Error", _e(), stacktrace)

    def _cast(self, out, peek=None):
        """ Try to convert the parameter into something WSGI compatible and set
        correct HTTP headers when possible.
        Support: False, str, unicode, dict, HTTPResponse, HTTPError, file-like,
        iterable of strings and iterable of unicodes
        """

        # Empty output is done here
        if not out:
            if 'Content-Length' not in response:
                response['Content-Length'] = 0
            return []
        # Join lists of byte or unicode strings. Mixed lists are NOT supported
        if isinstance(out, (tuple, list))\
        and isinstance(out[0], (bytes, unicode)):
            out = out[0][0:0].join(out) # b'abc'[0:0] -> b''
        # Encode unicode strings
        if isinstance(out, unicode):
            out = out.encode(response.charset)
        # Byte Strings are just returned
        if isinstance(out, bytes):
            if 'Content-Length' not in response:
                response['Content-Length'] = len(out)
            return [out]
        # HTTPError or HTTPException (recursive, because they may wrap anything)
        # TODO: Handle these explicitly in handle() or make them iterable.
        if isinstance(out, HTTPError):
            out.apply(response)
            out = self.error_handler.get(out.status_code, self.default_error_handler)(out)
            return self._cast(out)
        if isinstance(out, HTTPResponse):
            out.apply(response)
            return self._cast(out.body)

        # File-like objects.
        if hasattr(out, 'read'):
            if 'wsgi.file_wrapper' in request.environ:
                return request.environ['wsgi.file_wrapper'](out)
            elif hasattr(out, 'close') or not hasattr(out, '__iter__'):
                return WSGIFileWrapper(out)

        # Handle Iterables. We peek into them to detect their inner type.
        try:
            iout = iter(out)
            first = next(iout)
            while not first:
                first = next(iout)
        except StopIteration:
            return self._cast('')
        except HTTPResponse:
            first = _e()
        except (KeyboardInterrupt, SystemExit, MemoryError):
            raise
        except Exception:
            if not self.catchall: raise
            first = HTTPError(500, 'Unhandled exception', _e(), format_exc())

        # These are the inner types allowed in iterator or generator objects.
        if isinstance(first, HTTPResponse):
            return self._cast(first)
        elif isinstance(first, bytes):
            new_iter = itertools.chain([first], iout)
        elif isinstance(first, unicode):
            encoder = lambda x: x.encode(response.charset)
            new_iter = imap(encoder, itertools.chain([first], iout))
        else:
            msg = 'Unsupported response type: %s' % type(first)
            return self._cast(HTTPError(500, msg))
        if hasattr(out, 'close'):
            new_iter = _closeiter(new_iter, out.close)
        return new_iter

    def wsgi(self, environ, start_response):
        """ The bottle WSGI-interface. """
        try:
            out = self._cast(self._handle(environ))
            # rfc2616 section 4.3
            if response._status_code in (100, 101, 204, 304)\
            or environ['REQUEST_METHOD'] == 'HEAD':
                if hasattr(out, 'close'): out.close()
                out = []
            start_response(response._status_line, response.headerlist)
            return out
        except (KeyboardInterrupt, SystemExit, MemoryError):
            raise
        except Exception:
            if not self.catchall: raise
            err = '<h1>Critical error while processing request: %s</h1>' \
                  % html_escape(environ.get('PATH_INFO', '/'))
            if DEBUG:
                err += '<h2>Error:</h2>\n<pre>\n%s\n</pre>\n' \
                       '<h2>Traceback:</h2>\n<pre>\n%s\n</pre>\n' \
                       % (html_escape(repr(_e())), html_escape(format_exc()))
            environ['wsgi.errors'].write(err)
            headers = [('Content-Type', 'text/html; charset=UTF-8')]
            start_response('500 INTERNAL SERVER ERROR', headers, sys.exc_info())
            return [tob(err)]

    def __call__(self, environ, start_response):
        ''' Each instance of :class:'Bottle' is a WSGI application. '''
        return self.wsgi(environ, start_response)

    def __enter__(self):
        ''' Use this application as default for all module-level shortcuts. '''
        default_app.push(self)
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        default_app.pop()





###############################################################################
# HTTP and WSGI Tools ##########################################################
###############################################################################

class BaseRequest(object):
    """ A wrapper for WSGI environment dictionaries that adds a lot of
        convenient access methods and properties. Most of them are read-only.

        Adding new attributes to a request actually adds them to the environ
        dictionary (as 'bottle.request.ext.<name>'). This is the recommended
        way to store and access request-specific data.
    """

    __slots__ = ('environ')

    #: Maximum size of memory buffer for :attr:`body` in bytes.
    MEMFILE_MAX = 102400

    def __init__(self, environ=None):
        """ Wrap a WSGI environ dictionary. """
        #: The wrapped WSGI environ dictionary. This is the only real attribute.
        #: All other attributes actually are read-only properties.
        self.environ = {} if environ is None else environ
        self.environ['bottle.request'] = self

    @DictProperty('environ', 'bottle.app', read_only=True)
    def app(self):
        ''' Bottle application handling this request. '''
        raise RuntimeError('This request is not connected to an application.')

    @DictProperty('environ', 'bottle.route', read_only=True)
    def route(self):
        """ The bottle :class:`Route` object that matches this request. """
        raise RuntimeError('This request is not connected to a route.')

    @DictProperty('environ', 'route.url_args', read_only=True)
    def url_args(self):
        """ The arguments extracted from the URL. """
        raise RuntimeError('This request is not connected to a route.')

    @property
    def path(self):
        ''' The value of ``PATH_INFO`` with exactly one prefixed slash (to fix
            broken clients and avoid the "empty path" edge case). '''
        return '/' + self.environ.get('PATH_INFO','').lstrip('/')

    @property
    def method(self):
        ''' The ``REQUEST_METHOD`` value as an uppercase string. '''
        return self.environ.get('REQUEST_METHOD', 'GET').upper()

    @DictProperty('environ', 'bottle.request.headers', read_only=True)
    def headers(self):
        ''' A :class:`WSGIHeaderDict` that provides case-insensitive access to
            HTTP request headers. '''
        return WSGIHeaderDict(self.environ)

    def get_header(self, name, default=None):
        ''' Return the value of a request header, or a given default value. '''
        return self.headers.get(name, default)

    @DictProperty('environ', 'bottle.request.cookies', read_only=True)
    def cookies(self):
        """ Cookies parsed into a :class:`FormsDict`. Signed cookies are NOT
            decoded. Use :meth:`get_cookie` if you expect signed cookies. """
        cookies = SimpleCookie(self.environ.get('HTTP_COOKIE','')).values()
        return FormsDict((c.key, c.value) for c in cookies)

    def get_cookie(self, key, default=None, secret=None):
        """ Return the content of a cookie. To read a `Signed Cookie`, the
            `secret` must match the one used to create the cookie (see
            :meth:`BaseResponse.set_cookie`). If anything goes wrong (missing
            cookie or wrong signature), return a default value. """
        value = self.cookies.get(key)
        if secret and value:
            dec = cookie_decode(value, secret) # (key, value) tuple or None
            return dec[1] if dec and dec[0] == key else default
        return value or default

    @DictProperty('environ', 'bottle.request.query', read_only=True)
    def query(self):
        ''' The :attr:`query_string` parsed into a :class:`FormsDict`. These
            values are sometimes called "URL arguments" or "GET parameters", but
            not to be confused with "URL wildcards" as they are provided by the
            :class:`Router`. '''
        get = self.environ['bottle.get'] = FormsDict()
        pairs = _parse_qsl(self.environ.get('QUERY_STRING', ''))
        for key, value in pairs:
            get[key] = value
        return get

    @DictProperty('environ', 'bottle.request.forms', read_only=True)
    def forms(self):
        """ Form values parsed from an `url-encoded` or `multipart/form-data`
            encoded POST or PUT request body. The result is returned as a
            :class:`FormsDict`. All keys and values are strings. File uploads
            are stored separately in :attr:`files`. """
        forms = FormsDict()
        for name, item in self.POST.allitems():
            if not isinstance(item, FileUpload):
                forms[name] = item
        return forms

    @DictProperty('environ', 'bottle.request.params', read_only=True)
    def params(self):
        """ A :class:`FormsDict` with the combined values of :attr:`query` and
            :attr:`forms`. File uploads are stored in :attr:`files`. """
        params = FormsDict()
        for key, value in self.query.allitems():
            params[key] = value
        for key, value in self.forms.allitems():
            params[key] = value
        return params

    @DictProperty('environ', 'bottle.request.files', read_only=True)
    def files(self):
        """ File uploads parsed from `multipart/form-data` encoded POST or PUT
            request body. The values are instances of :class:`FileUpload`.

        """
        files = FormsDict()
        for name, item in self.POST.allitems():
            if isinstance(item, FileUpload):
                files[name] = item
        return files

    @DictProperty('environ', 'bottle.request.json', read_only=True)
    def json(self):
        ''' If the ``Content-Type`` header is ``application/json``, this
            property holds the parsed content of the request body. Only requests
            smaller than :attr:`MEMFILE_MAX` are processed to avoid memory
            exhaustion. '''
        if 'application/json' in self.environ.get('CONTENT_TYPE', ''):
            return json_loads(self._get_body_string())
        return None

    def _iter_body(self, read, bufsize):
        maxread = max(0, self.content_length)
        while maxread:
            part = read(min(maxread, bufsize))
            if not part: break
            yield part
            maxread -= len(part)

    def _iter_chunked(self, read, bufsize):
        err = HTTPError(400, 'Error while parsing chunked transfer body.')
        rn, sem, bs = tob('\r\n'), tob(';'), tob('')
        while True:
            header = read(1)
            while header[-2:] != rn:
                c = read(1)
                header += c
                if not c: raise err
                if len(header) > bufsize: raise err
            size, _, _ = header.partition(sem)
            try:
                maxread = int(tonat(size.strip()), 16)
            except ValueError:
                raise err
            if maxread == 0: break
            buff = bs
            while maxread > 0:
                if not buff:
                    buff = read(min(maxread, bufsize))
                part, buff = buff[:maxread], buff[maxread:]
                if not part: raise err
                yield part
                maxread -= len(part)
            if read(2) != rn:
                raise err
            
    @DictProperty('environ', 'bottle.request.body', read_only=True)
    def _body(self):
        body_iter = self._iter_chunked if self.chunked else self._iter_body
        read_func = self.environ['wsgi.input'].read
        body, body_size, is_temp_file = BytesIO(), 0, False
        for part in body_iter(read_func, self.MEMFILE_MAX):
            body.write(part)
            body_size += len(part)
            if not is_temp_file and body_size > self.MEMFILE_MAX:
                body, tmp = TemporaryFile(mode='w+b'), body
                body.write(tmp.getvalue())
                del tmp
                is_temp_file = True
        self.environ['wsgi.input'] = body
        body.seek(0)
        return body

    def _get_body_string(self):
        ''' read body until content-length or MEMFILE_MAX into a string. Raise
            HTTPError(413) on requests that are to large. '''
        clen = self.content_length
        if clen > self.MEMFILE_MAX:
            raise HTTPError(413, 'Request to large')
        if clen < 0: clen = self.MEMFILE_MAX + 1
        data = self.body.read(clen)
        if len(data) > self.MEMFILE_MAX: # Fail fast
            raise HTTPError(413, 'Request to large')
        return data

    @property
    def body(self):
        """ The HTTP request body as a seek-able file-like object. Depending on
            :attr:`MEMFILE_MAX`, this is either a temporary file or a
            :class:`io.BytesIO` instance. Accessing this property for the first
            time reads and replaces the ``wsgi.input`` environ variable.
            Subsequent accesses just do a `seek(0)` on the file object. """
        self._body.seek(0)
        return self._body

    @property
    def chunked(self):
        ''' True if Chunked transfer encoding was. '''
        return 'chunked' in self.environ.get('HTTP_TRANSFER_ENCODING', '').lower()

    #: An alias for :attr:`query`.
    GET = query

    @DictProperty('environ', 'bottle.request.post', read_only=True)
    def POST(self):
        """ The values of :attr:`forms` and :attr:`files` combined into a single
            :class:`FormsDict`. Values are either strings (form values) or
            instances of :class:`cgi.FieldStorage` (file uploads).
        """
        post = FormsDict()
        # We default to application/x-www-form-urlencoded for everything that
        # is not multipart and take the fast path (also: 3.1 workaround)
        if not self.content_type.startswith('multipart/'):
            pairs = _parse_qsl(tonat(self._get_body_string(), 'latin1'))
            for key, value in pairs:
                post[key] = value
            return post

        safe_env = {'QUERY_STRING':''} # Build a safe environment for cgi
        for key in ('REQUEST_METHOD', 'CONTENT_TYPE', 'CONTENT_LENGTH'):
            if key in self.environ: safe_env[key] = self.environ[key]
        args = dict(fp=self.body, environ=safe_env, keep_blank_values=True)
        if py31:
            args['fp'] = NCTextIOWrapper(args['fp'], encoding='utf8',
                                         newline='\n')
        elif py3k:
            args['encoding'] = 'utf8'
        data = cgi.FieldStorage(**args)
        data = data.list or []
        for item in data:
            if item.filename:
                post[item.name] = FileUpload(item.file, item.name,
                                             item.filename, item.headers)
            else:
                post[item.name] = item.value
        return post

    @property
    def url(self):
        """ The full request URI including hostname and scheme. If your app
            lives behind a reverse proxy or load balancer and you get confusing
            results, make sure that the ``X-Forwarded-Host`` header is set
            correctly. """
        return self.urlparts.geturl()

    @DictProperty('environ', 'bottle.request.urlparts', read_only=True)
    def urlparts(self):
        ''' The :attr:`url` string as an :class:`urlparse.SplitResult` tuple.
            The tuple contains (scheme, host, path, query_string and fragment),
            but the fragment is always empty because it is not visible to the
            server. '''
        env = self.environ
        http = env.get('HTTP_X_FORWARDED_PROTO') or env.get('wsgi.url_scheme', 'http')
        host = env.get('HTTP_X_FORWARDED_HOST') or env.get('HTTP_HOST')
        if not host:
            # HTTP 1.1 requires a Host-header. This is for HTTP/1.0 clients.
            host = env.get('SERVER_NAME', '127.0.0.1')
            port = env.get('SERVER_PORT')
            if port and port != ('80' if http == 'http' else '443'):
                host += ':' + port
        path = urlquote(self.fullpath)
        return UrlSplitResult(http, host, path, env.get('QUERY_STRING'), '')

    @property
    def fullpath(self):
        """ Request path including :attr:`script_name` (if present). """
        return urljoin(self.script_name, self.path.lstrip('/'))

    @property
    def query_string(self):
        """ The raw :attr:`query` part of the URL (everything in between ``?``
            and ``#``) as a string. """
        return self.environ.get('QUERY_STRING', '')

    @property
    def script_name(self):
        ''' The initial portion of the URL's `path` that was removed by a higher
            level (server or routing middleware) before the application was
            called. This script path is returned with leading and tailing
            slashes. '''
        script_name = self.environ.get('SCRIPT_NAME', '').strip('/')
        return '/' + script_name + '/' if script_name else '/'

    def path_shift(self, shift=1):
        ''' Shift path segments from :attr:`path` to :attr:`script_name` and
            vice versa.

           :param shift: The number of path segments to shift. May be negative
                         to change the shift direction. (default: 1)
        '''
        script = self.environ.get('SCRIPT_NAME','/')
        self['SCRIPT_NAME'], self['PATH_INFO'] = path_shift(script, self.path, shift)

    @property
    def content_length(self):
        ''' The request body length as an integer. The client is responsible to
            set this header. Otherwise, the real length of the body is unknown
            and -1 is returned. In this case, :attr:`body` will be empty. '''
        return int(self.environ.get('CONTENT_LENGTH') or -1)

    @property
    def content_type(self):
        ''' The Content-Type header as a lowercase-string (default: empty). '''
        return self.environ.get('CONTENT_TYPE', '').lower()

    @property
    def is_xhr(self):
        ''' True if the request was triggered by a XMLHttpRequest. This only
            works with JavaScript libraries that support the `X-Requested-With`
            header (most of the popular libraries do). '''
        requested_with = self.environ.get('HTTP_X_REQUESTED_WITH','')
        return requested_with.lower() == 'xmlhttprequest'

    @property
    def is_ajax(self):
        ''' Alias for :attr:`is_xhr`. "Ajax" is not the right term. '''
        return self.is_xhr

    @property
    def auth(self):
        """ HTTP authentication data as a (user, password) tuple. This
            implementation currently supports basic (not digest) authentication
            only. If the authentication happened at a higher level (e.g. in the
            front web-server or a middleware), the password field is None, but
            the user field is looked up from the ``REMOTE_USER`` environ
            variable. On any errors, None is returned. """
        basic = parse_auth(self.environ.get('HTTP_AUTHORIZATION',''))
        if basic: return basic
        ruser = self.environ.get('REMOTE_USER')
        if ruser: return (ruser, None)
        return None

    @property
    def remote_route(self):
        """ A list of all IPs that were involved in this request, starting with
            the client IP and followed by zero or more proxies. This does only
            work if all proxies support the ```X-Forwarded-For`` header. Note
            that this information can be forged by malicious clients. """
        proxy = self.environ.get('HTTP_X_FORWARDED_FOR')
        if proxy: return [ip.strip() for ip in proxy.split(',')]
        remote = self.environ.get('REMOTE_ADDR')
        return [remote] if remote else []

    @property
    def remote_addr(self):
        """ The client IP as a string. Note that this information can be forged
            by malicious clients. """
        route = self.remote_route
        return route[0] if route else None

    def copy(self):
        """ Return a new :class:`Request` with a shallow :attr:`environ` copy. """
        return Request(self.environ.copy())

    def get(self, value, default=None): return self.environ.get(value, default)
    def __getitem__(self, key): return self.environ[key]
    def __delitem__(self, key): self[key] = ""; del(self.environ[key])
    def __iter__(self): return iter(self.environ)
    def __len__(self): return len(self.environ)
    def keys(self): return self.environ.keys()
    def __setitem__(self, key, value):
        """ Change an environ value and clear all caches that depend on it. """

        if self.environ.get('bottle.request.readonly'):
            raise KeyError('The environ dictionary is read-only.')

        self.environ[key] = value
        todelete = ()

        if key == 'wsgi.input':
            todelete = ('body', 'forms', 'files', 'params', 'post', 'json')
        elif key == 'QUERY_STRING':
            todelete = ('query', 'params')
        elif key.startswith('HTTP_'):
            todelete = ('headers', 'cookies')

        for key in todelete:
            self.environ.pop('bottle.request.'+key, None)

    def __repr__(self):
        return '<%s: %s %s>' % (self.__class__.__name__, self.method, self.url)

    def __getattr__(self, name):
        ''' Search in self.environ for additional user defined attributes. '''
        try:
            var = self.environ['bottle.request.ext.%s'%name]
            return var.__get__(self) if hasattr(var, '__get__') else var
        except KeyError:
            raise AttributeError('Attribute %r not defined.' % name)

    def __setattr__(self, name, value):
        if name == 'environ': return object.__setattr__(self, name, value)
        self.environ['bottle.request.ext.%s'%name] = value




def _hkey(s):
    return s.title().replace('_','-')


class HeaderProperty(object):
    def __init__(self, name, reader=None, writer=str, default=''):
        self.name, self.default = name, default
        self.reader, self.writer = reader, writer
        self.__doc__ = 'Current value of the %r header.' % name.title()

    def __get__(self, obj, cls):
        if obj is None: return self
        value = obj.headers.get(self.name, self.default)
        return self.reader(value) if self.reader else value

    def __set__(self, obj, value):
        obj.headers[self.name] = self.writer(value)

    def __delete__(self, obj):
        del obj.headers[self.name]


class BaseResponse(object):
    """ Storage class for a response body as well as headers and cookies.

        This class does support dict-like case-insensitive item-access to
        headers, but is NOT a dict. Most notably, iterating over a response
        yields parts of the body and not the headers.

        :param body: The response body as one of the supported types.
        :param status: Either an HTTP status code (e.g. 200) or a status line
                       including the reason phrase (e.g. '200 OK').
        :param headers: A dictionary or a list of name-value pairs.

        Additional keyword arguments are added to the list of headers.
        Underscores in the header name are replaced with dashes.
    """

    default_status = 200
    default_content_type = 'text/html; charset=UTF-8'

    # Header blacklist for specific response codes
    # (rfc2616 section 10.2.3 and 10.3.5)
    bad_headers = {
        204: set(('Content-Type',)),
        304: set(('Allow', 'Content-Encoding', 'Content-Language',
                  'Content-Length', 'Content-Range', 'Content-Type',
                  'Content-Md5', 'Last-Modified'))}

    def __init__(self, body='', status=None, headers=None, **more_headers):
        self._cookies = None
        self._headers = {}
        self.body = body
        self.status = status or self.default_status
        if headers:
            if isinstance(headers, dict):
                headers = headers.items()
            for name, value in headers:
                self.add_header(name, value)
        if more_headers:
            for name, value in more_headers.items():
                self.add_header(name, value)

    def copy(self, cls=None):
        ''' Returns a copy of self. '''
        cls = cls or BaseResponse
        assert issubclass(cls, BaseResponse)
        copy = cls()
        copy.status = self.status
        copy._headers = dict((k, v[:]) for (k, v) in self._headers.items())
        if self._cookies:
            copy._cookies = SimpleCookie()
            copy._cookies.load(self._cookies.output())
        return copy

    def __iter__(self):
        return iter(self.body)

    def close(self):
        if hasattr(self.body, 'close'):
            self.body.close()

    @property
    def status_line(self):
        ''' The HTTP status line as a string (e.g. ``404 Not Found``).'''
        return self._status_line

    @property
    def status_code(self):
        ''' The HTTP status code as an integer (e.g. 404).'''
        return self._status_code

    def _set_status(self, status):
        if isinstance(status, int):
            code, status = status, _HTTP_STATUS_LINES.get(status)
        elif ' ' in status:
            status = status.strip()
            code   = int(status.split()[0])
        else:
            raise ValueError('String status line without a reason phrase.')
        if not 100 <= code <= 999: raise ValueError('Status code out of range.')
        self._status_code = code
        self._status_line = str(status or ('%d Unknown' % code))

    def _get_status(self):
        return self._status_line

    status = property(_get_status, _set_status, None,
        ''' A writeable property to change the HTTP response status. It accepts
            either a numeric code (100-999) or a string with a custom reason
            phrase (e.g. "404 Brain not found"). Both :data:`status_line` and
            :data:`status_code` are updated accordingly. The return value is
            always a status string. ''')
    del _get_status, _set_status

    @property
    def headers(self):
        ''' An instance of :class:`HeaderDict`, a case-insensitive dict-like
            view on the response headers. '''
        hdict = HeaderDict()
        hdict.dict = self._headers
        return hdict

    def __contains__(self, name): return _hkey(name) in self._headers
    def __delitem__(self, name):  del self._headers[_hkey(name)]
    def __getitem__(self, name):  return self._headers[_hkey(name)][-1]
    def __setitem__(self, name, value): self._headers[_hkey(name)] = [str(value)]

    def get_header(self, name, default=None):
        ''' Return the value of a previously defined header. If there is no
            header with that name, return a default value. '''
        return self._headers.get(_hkey(name), [default])[-1]

    def set_header(self, name, value):
        ''' Create a new response header, replacing any previously defined
            headers with the same name. '''
        self._headers[_hkey(name)] = [str(value)]

    def add_header(self, name, value):
        ''' Add an additional response header, not removing duplicates. '''
        self._headers.setdefault(_hkey(name), []).append(str(value))

    def iter_headers(self):
        ''' Yield (header, value) tuples, skipping headers that are not
            allowed with the current response status code. '''
        return self.headerlist

    @property
    def headerlist(self):
        ''' WSGI conform list of (header, value) tuples. '''
        out = []
        headers = list(self._headers.items())
        if 'Content-Type' not in self._headers:
            headers.append(('Content-Type', [self.default_content_type]))
        if self._status_code in self.bad_headers:
            bad_headers = self.bad_headers[self._status_code]
            headers = [h for h in headers if h[0] not in bad_headers]
        out += [(name, val) for name, vals in headers for val in vals]
        if self._cookies:
            for c in self._cookies.values():
                out.append(('Set-Cookie', c.OutputString()))
        return out

    content_type = HeaderProperty('Content-Type')
    content_length = HeaderProperty('Content-Length', reader=int)
    expires = HeaderProperty('Expires',
        reader=lambda x: datetime.utcfromtimestamp(parse_date(x)),
        writer=lambda x: http_date(x))

    @property
    def charset(self, default='UTF-8'):
        """ Return the charset specified in the content-type header (default: utf8). """
        if 'charset=' in self.content_type:
            return self.content_type.split('charset=')[-1].split(';')[0].strip()
        return default

    def set_cookie(self, name, value, secret=None, **options):
        ''' Create a new cookie or replace an old one. If the `secret` parameter is
            set, create a `Signed Cookie` (described below).

            :param name: the name of the cookie.
            :param value: the value of the cookie.
            :param secret: a signature key required for signed cookies.

            Additionally, this method accepts all RFC 2109 attributes that are
            supported by :class:`cookie.Morsel`, including:

            :param max_age: maximum age in seconds. (default: None)
            :param expires: a datetime object or UNIX timestamp. (default: None)
            :param domain: the domain that is allowed to read the cookie.
              (default: current domain)
            :param path: limits the cookie to a given path (default: current path)
            :param secure: limit the cookie to HTTPS connections (default: off).
            :param httponly: prevents client-side javascript to read this cookie
              (default: off, requires Python 2.6 or newer).

            If neither `expires` nor `max_age` is set (default), the cookie will
            expire at the end of the browser session (as soon as the browser
            window is closed).

            Signed cookies may store any pickle-able object and are
            cryptographically signed to prevent manipulation. Keep in mind that
            cookies are limited to 4kb in most browsers.

            Warning: Signed cookies are not encrypted (the client can still see
            the content) and not copy-protected (the client can restore an old
            cookie). The main intention is to make pickling and unpickling
            save, not to store secret information at client side.
        '''
        if not self._cookies:
            self._cookies = SimpleCookie()

        if secret:
            value = touni(cookie_encode((name, value), secret))
        elif not isinstance(value, basestring):
            raise TypeError('Secret key missing for non-string Cookie.')

        if len(value) > 4096: raise ValueError('Cookie value to long.')
        self._cookies[name] = value

        for key, value in options.items():
            if key == 'max_age':
                if isinstance(value, timedelta):
                    value = value.seconds + value.days * 24 * 3600
            if key == 'expires':
                if isinstance(value, (datedate, datetime)):
                    value = value.timetuple()
                elif isinstance(value, (int, float)):
                    value = time.gmtime(value)
                value = time.strftime("%a, %d %b %Y %H:%M:%S GMT", value)
            self._cookies[name][key.replace('_', '-')] = value

    def delete_cookie(self, key, **kwargs):
        ''' Delete a cookie. Be sure to use the same `domain` and `path`
            settings as used to create the cookie. '''
        kwargs['max_age'] = -1
        kwargs['expires'] = 0
        self.set_cookie(key, '', **kwargs)

    def __repr__(self):
        out = ''
        for name, value in self.headerlist:
            out += '%s: %s\n' % (name.title(), value.strip())
        return out


def _local_property():
    ls = threading.local()
    def fget(self):
        try: return ls.var
        except AttributeError:
            raise RuntimeError("Request context not initialized.")
    def fset(self, value): ls.var = value
    def fdel(self): del ls.var
    return property(fget, fset, fdel, 'Thread-local property')


class LocalRequest(BaseRequest):
    ''' A thread-local subclass of :class:`BaseRequest` with a different
        set of attributes for each thread. There is usually only one global
        instance of this class (:data:`request`). If accessed during a
        request/response cycle, this instance always refers to the *current*
        request (even on a multithreaded server). '''
    bind = BaseRequest.__init__
    environ = _local_property()


class LocalResponse(BaseResponse):
    ''' A thread-local subclass of :class:`BaseResponse` with a different
        set of attributes for each thread. There is usually only one global
        instance of this class (:data:`response`). Its attributes are used
        to build the HTTP response at the end of the request/response cycle.
    '''
    bind = BaseResponse.__init__
    _status_line = _local_property()
    _status_code = _local_property()
    _cookies     = _local_property()
    _headers     = _local_property()
    body         = _local_property()


Request = BaseRequest
Response = BaseResponse


class HTTPResponse(Response, BottleException):
    def __init__(self, body='', status=None, headers=None, **more_headers):
        super(HTTPResponse, self).__init__(body, status, headers, **more_headers)

    def apply(self, response):
        response._status_code = self._status_code
        response._status_line = self._status_line
        response._headers = self._headers
        response._cookies = self._cookies
        response.body = self.body


class HTTPError(HTTPResponse):
    default_status = 500
    def __init__(self, status=None, body=None, exception=None, traceback=None,
                 **options):
        self.exception = exception
        self.traceback = traceback
        super(HTTPError, self).__init__(body, status, **options)





###############################################################################
# Plugins ######################################################################
###############################################################################

class PluginError(BottleException): pass


class JSONPlugin(object):
    name = 'json'
    api  = 2

    def __init__(self, json_dumps=json_dumps):
        self.json_dumps = json_dumps

    def apply(self, callback, route):
        dumps = self.json_dumps
        if not dumps: return callback
        def wrapper(*a, **ka):
            try:
                rv = callback(*a, **ka)
            except HTTPError:
                rv = _e()

            if isinstance(rv, dict):
                #Attempt to serialize, raises exception on failure
                json_response = dumps(rv)
                #Set content type only if serialization succesful
                response.content_type = 'application/json'
                return json_response
            elif isinstance(rv, HTTPResponse) and isinstance(rv.body, dict):
                rv.body = dumps(rv.body)
                rv.content_type = 'application/json'
            return rv

        return wrapper


class TemplatePlugin(object):
    ''' This plugin applies the :func:`view` decorator to all routes with a
        `template` config parameter. If the parameter is a tuple, the second
        element must be a dict with additional options (e.g. `template_engine`)
        or default variables for the template. '''
    name = 'template'
    api  = 2

    def apply(self, callback, route):
        conf = route.config.get('template')
        if isinstance(conf, (tuple, list)) and len(conf) == 2:
            return view(conf[0], **conf[1])(callback)
        elif isinstance(conf, str):
            return view(conf)(callback)
        else:
            return callback


#: Not a plugin, but part of the plugin API. TODO: Find a better place.
class _ImportRedirect(object):
    def __init__(self, name, impmask):
        ''' Create a virtual package that redirects imports (see PEP 302). '''
        self.name = name
        self.impmask = impmask
        self.module = sys.modules.setdefault(name, imp.new_module(name))
        self.module.__dict__.update({'__file__': __file__, '__path__': [],
                                    '__all__': [], '__loader__': self})
        sys.meta_path.append(self)

    def find_module(self, fullname, path=None):
        if '.' not in fullname: return
        packname = fullname.rsplit('.', 1)[0]
        if packname != self.name: return
        return self

    def load_module(self, fullname):
        if fullname in sys.modules: return sys.modules[fullname]
        modname = fullname.rsplit('.', 1)[1]
        realname = self.impmask % modname
        __import__(realname)
        module = sys.modules[fullname] = sys.modules[realname]
        setattr(self.module, modname, module)
        module.__loader__ = self
        return module






###############################################################################
# Common Utilities #############################################################
###############################################################################


class MultiDict(DictMixin):
    """ This dict stores multiple values per key, but behaves exactly like a
        normal dict in that it returns only the newest value for any given key.
        There are special methods available to access the full list of values.
    """

    def __init__(self, *a, **k):
        self.dict = dict((k, [v]) for (k, v) in dict(*a, **k).items())

    def __len__(self): return len(self.dict)
    def __iter__(self): return iter(self.dict)
    def __contains__(self, key): return key in self.dict
    def __delitem__(self, key): del self.dict[key]
    def __getitem__(self, key): return self.dict[key][-1]
    def __setitem__(self, key, value): self.append(key, value)
    def keys(self): return self.dict.keys()

    if py3k:
        def values(self): return (v[-1] for v in self.dict.values())
        def items(self): return ((k, v[-1]) for k, v in self.dict.items())
        def allitems(self):
            return ((k, v) for k, vl in self.dict.items() for v in vl)
        iterkeys = keys
        itervalues = values
        iteritems = items
        iterallitems = allitems

    else:
        def values(self): return [v[-1] for v in self.dict.values()]
        def items(self): return [(k, v[-1]) for k, v in self.dict.items()]
        def iterkeys(self): return self.dict.iterkeys()
        def itervalues(self): return (v[-1] for v in self.dict.itervalues())
        def iteritems(self):
            return ((k, v[-1]) for k, v in self.dict.iteritems())
        def iterallitems(self):
            return ((k, v) for k, vl in self.dict.iteritems() for v in vl)
        def allitems(self):
            return [(k, v) for k, vl in self.dict.iteritems() for v in vl]

    def get(self, key, default=None, index=-1, type=None):
        ''' Return the most recent value for a key.

            :param default: The default value to be returned if the key is not
                   present or the type conversion fails.
            :param index: An index for the list of available values.
            :param type: If defined, this callable is used to cast the value
                    into a specific type. Exception are suppressed and result in
                    the default value to be returned.
        '''
        try:
            val = self.dict[key][index]
            return type(val) if type else val
        except Exception:
            pass
        return default

    def append(self, key, value):
        ''' Add a new value to the list of values for this key. '''
        self.dict.setdefault(key, []).append(value)

    def replace(self, key, value):
        ''' Replace the list of values with a single value. '''
        self.dict[key] = [value]

    def getall(self, key):
        ''' Return a (possibly empty) list of values for a key. '''
        return self.dict.get(key) or []

    #: Aliases for WTForms to mimic other multi-dict APIs (Django)
    getone = get
    getlist = getall


class FormsDict(MultiDict):
    ''' This :class:`MultiDict` subclass is used to store request form data.
        Additionally to the normal dict-like item access methods (which return
        unmodified data as native strings), this container also supports
        attribute-like access to its values. Attributes are automatically de-
        or recoded to match :attr:`input_encoding` (default: 'utf8'). Missing
        attributes default to an empty string. '''

    #: Encoding used for attribute values.
    input_encoding = 'utf8'
    #: If true (default), unicode strings are first encoded with `latin1`
    #: and then decoded to match :attr:`input_encoding`.
    recode_unicode = True

    def _fix(self, s, encoding=None):
        if isinstance(s, unicode) and self.recode_unicode: # Python 3 WSGI
            return s.encode('latin1').decode(encoding or self.input_encoding)
        elif isinstance(s, bytes): # Python 2 WSGI
            return s.decode(encoding or self.input_encoding)
        else:
            return s

    def decode(self, encoding=None):
        ''' Returns a copy with all keys and values de- or recoded to match
            :attr:`input_encoding`. Some libraries (e.g. WTForms) want a
            unicode dictionary. '''
        copy = FormsDict()
        enc = copy.input_encoding = encoding or self.input_encoding
        copy.recode_unicode = False
        for key, value in self.allitems():
            copy.append(self._fix(key, enc), self._fix(value, enc))
        return copy

    def getunicode(self, name, default=None, encoding=None):
        ''' Return the value as a unicode string, or the default. '''
        try:
            return self._fix(self[name], encoding)
        except (UnicodeError, KeyError):
            return default

    def __getattr__(self, name, default=unicode()):
        # Without this guard, pickle generates a cryptic TypeError:
        if name.startswith('__') and name.endswith('__'):
            return super(FormsDict, self).__getattr__(name)
        return self.getunicode(name, default=default)


class HeaderDict(MultiDict):
    """ A case-insensitive version of :class:`MultiDict` that defaults to
        replace the old value instead of appending it. """

    def __init__(self, *a, **ka):
        self.dict = {}
        if a or ka: self.update(*a, **ka)

    def __contains__(self, key): return _hkey(key) in self.dict
    def __delitem__(self, key): del self.dict[_hkey(key)]
    def __getitem__(self, key): return self.dict[_hkey(key)][-1]
    def __setitem__(self, key, value): self.dict[_hkey(key)] = [str(value)]
    def append(self, key, value):
        self.dict.setdefault(_hkey(key), []).append(str(value))
    def replace(self, key, value): self.dict[_hkey(key)] = [str(value)]
    def getall(self, key): return self.dict.get(_hkey(key)) or []
    def get(self, key, default=None, index=-1):
        return MultiDict.get(self, _hkey(key), default, index)
    def filter(self, names):
        for name in [_hkey(n) for n in names]:
            if name in self.dict:
                del self.dict[name]


class WSGIHeaderDict(DictMixin):
    ''' This dict-like class wraps a WSGI environ dict and provides convenient
        access to HTTP_* fields. Keys and values are native strings
        (2.x bytes or 3.x unicode) and keys are case-insensitive. If the WSGI
        environment contains non-native string values, these are de- or encoded
        using a lossless 'latin1' character set.

        The API will remain stable even on changes to the relevant PEPs.
        Currently PEP 333, 444 and 3333 are supported. (PEP 444 is the only one
        that uses non-native strings.)
    '''
    #: List of keys that do not have a ``HTTP_`` prefix.
    cgikeys = ('CONTENT_TYPE', 'CONTENT_LENGTH')

    def __init__(self, environ):
        self.environ = environ

    def _ekey(self, key):
        ''' Translate header field name to CGI/WSGI environ key. '''
        key = key.replace('-','_').upper()
        if key in self.cgikeys:
            return key
        return 'HTTP_' + key

    def raw(self, key, default=None):
        ''' Return the header value as is (may be bytes or unicode). '''
        return self.environ.get(self._ekey(key), default)

    def __getitem__(self, key):
        return tonat(self.environ[self._ekey(key)], 'latin1')

    def __setitem__(self, key, value):
        raise TypeError("%s is read-only." % self.__class__)

    def __delitem__(self, key):
        raise TypeError("%s is read-only." % self.__class__)

    def __iter__(self):
        for key in self.environ:
            if key[:5] == 'HTTP_':
                yield key[5:].replace('_', '-').title()
            elif key in self.cgikeys:
                yield key.replace('_', '-').title()

    def keys(self): return [x for x in self]
    def __len__(self): return len(self.keys())
    def __contains__(self, key): return self._ekey(key) in self.environ



class ConfigDict(dict):
    ''' A dict-like configuration storage with additional support for
        namespaces, validators, meta-data, on_change listeners and more.
    '''

    __slots__ = ('_meta', '_on_change')

    def __init__(self):
        self._meta = {}
        self._on_change = lambda name, value: None

    def load_config(self, filename):
        ''' Load values from an ``*.ini`` style config file.

            If the config file contains sections, their names are used as
            namespaces for the values within. The two special sections
            ``DEFAULT`` and ``bottle`` refer to the root namespace (no prefix).
        '''
        conf = ConfigParser()
        conf.read(filename)
        for section in conf.sections():
            for key, value in conf.items(section):
                if section not in ('DEFAULT', 'bottle'):
                    key = section + '.' + key
                self[key] = value
        return self

    def load_dict(self, source, namespace=''):
        ''' Load values from a dictionary structure. Nesting can be used to
            represent namespaces.

            >>> c = ConfigDict()
            >>> c.load_dict({'some': {'namespace': {'key': 'value'} } })
            {'some.namespace.key': 'value'}            
        '''
        for key, value in source.items():
            if isinstance(key, str):
                nskey = (namespace + '.' + key).strip('.')
                if isinstance(value, dict):
                    self.load_dict(value, namespace=nskey)
                else:
                    self[nskey] = value
            else:
                raise TypeError('Key has type %r (not a string)' % type(key))
        return self

    def update(self, *a, **ka):
        ''' If the first parameter is a string, all keys are prefixed with this
            namespace. Apart from that it works just as the usual dict.update().
            Example: ``update('some.namespace', key='value')`` '''
        prefix = ''
        if a and isinstance(a[0], str):
            prefix = a[0].strip('.') + '.'
            a = a[1:]
        for key, value in dict(*a, **ka).items():
            self[prefix+key] = value

    def setdefault(self, key, value):
        if key not in self:
            self[key] = value

    def __setitem__(self, key, value):
        if not isinstance(key, str):
            raise TypeError('Key has type %r (not a string)' % type(key))
        value = self.meta_get(key, 'filter', lambda x: x)(value)
        if key in self and self[key] is value:
            return
        self._on_change(key, value)
        dict.__setitem__(self, key, value)

    def __delitem__(self, key):
        self._on_change(key, None)
        dict.__delitem__(self, key)

    def meta_get(self, key, metafield, default=None):
        ''' Return the value of a meta field for a key. '''
        return self._meta.get(key, {}).get(metafield, default)

    def meta_set(self, key, metafield, value):
        ''' Set the meta field for a key to a new value. This triggers the
            on-change handler for existing keys. '''
        self._meta.setdefault(key, {})[metafield] = value
        if key in self:
            self[key] = self[key]

    def meta_list(self, key):
        ''' Return an iterable of meta field names defined for a key. '''
        return self._meta.get(key, {}).keys()


class AppStack(list):
    """ A stack-like list. Calling it returns the head of the stack. """

    def __call__(self):
        """ Return the current default application. """
        return self[-1]

    def push(self, value=None):
        """ Add a new :class:`Bottle` instance to the stack """
        if not isinstance(value, Bottle):
            value = Bottle()
        self.append(value)
        return value


class WSGIFileWrapper(object):

    def __init__(self, fp, buffer_size=1024*64):
        self.fp, self.buffer_size = fp, buffer_size
        for attr in ('fileno', 'close', 'read', 'readlines', 'tell', 'seek'):
            if hasattr(fp, attr): setattr(self, attr, getattr(fp, attr))

    def __iter__(self):
        buff, read = self.buffer_size, self.read
        while True:
            part = read(buff)
            if not part: return
            yield part


class _closeiter(object):
    ''' This only exists to be able to attach a .close method to iterators that
        do not support attribute assignment (most of itertools). '''

    def __init__(self, iterator, close=None):
        self.iterator = iterator
        self.close_callbacks = makelist(close)

    def __iter__(self):
        return iter(self.iterator)

    def close(self):
        for func in self.close_callbacks:
            func()


class ResourceManager(object):
    ''' This class manages a list of search paths and helps to find and open
        application-bound resources (files).

        :param base: default value for :meth:`add_path` calls.
        :param opener: callable used to open resources.
        :param cachemode: controls which lookups are cached. One of 'all',
                         'found' or 'none'.
    '''

    def __init__(self, base='./', opener=open, cachemode='all'):
        self.opener = open
        self.base = base
        self.cachemode = cachemode

        #: A list of search paths. See :meth:`add_path` for details.
        self.path = []
        #: A cache for resolved paths. ``res.cache.clear()`` clears the cache.
        self.cache = {}

    def add_path(self, path, base=None, index=None, create=False):
        ''' Add a new path to the list of search paths. Return False if the
            path does not exist.

            :param path: The new search path. Relative paths are turned into
                an absolute and normalized form. If the path looks like a file
                (not ending in `/`), the filename is stripped off.
            :param base: Path used to absolutize relative search paths.
                Defaults to :attr:`base` which defaults to ``os.getcwd()``.
            :param index: Position within the list of search paths. Defaults
                to last index (appends to the list).

            The `base` parameter makes it easy to reference files installed
            along with a python module or package::

                res.add_path('./resources/', __file__)
        '''
        base = os.path.abspath(os.path.dirname(base or self.base))
        path = os.path.abspath(os.path.join(base, os.path.dirname(path)))
        path += os.sep
        if path in self.path:
            self.path.remove(path)
        if create and not os.path.isdir(path):
            os.makedirs(path)
        if index is None:
            self.path.append(path)
        else:
            self.path.insert(index, path)
        self.cache.clear()
        return os.path.exists(path)

    def __iter__(self):
        ''' Iterate over all existing files in all registered paths. '''
        search = self.path[:]
        while search:
            path = search.pop()
            if not os.path.isdir(path): continue
            for name in os.listdir(path):
                full = os.path.join(path, name)
                if os.path.isdir(full): search.append(full)
                else: yield full

    def lookup(self, name):
        ''' Search for a resource and return an absolute file path, or `None`.

            The :attr:`path` list is searched in order. The first match is
            returend. Symlinks are followed. The result is cached to speed up
            future lookups. '''
        if name not in self.cache or DEBUG:
            for path in self.path:
                fpath = os.path.join(path, name)
                if os.path.isfile(fpath):
                    if self.cachemode in ('all', 'found'):
                        self.cache[name] = fpath
                    return fpath
            if self.cachemode == 'all':
                self.cache[name] = None
        return self.cache[name]

    def open(self, name, mode='r', *args, **kwargs):
        ''' Find a resource and return a file object, or raise IOError. '''
        fname = self.lookup(name)
        if not fname: raise IOError("Resource %r not found." % name)
        return self.opener(fname, mode=mode, *args, **kwargs)


class FileUpload(object):

    def __init__(self, fileobj, name, filename, headers=None):
        ''' Wrapper for file uploads. '''
        #: Open file(-like) object (BytesIO buffer or temporary file)
        self.file = fileobj
        #: Name of the upload form field
        self.name = name
        #: Raw filename as sent by the client (may contain unsafe characters)
        self.raw_filename = filename
        #: A :class:`HeaderDict` with additional headers (e.g. content-type)
        self.headers = HeaderDict(headers) if headers else HeaderDict()

    content_type = HeaderProperty('Content-Type')
    content_length = HeaderProperty('Content-Length', reader=int, default=-1)

    @cached_property
    def filename(self):
        ''' Name of the file on the client file system, but normalized to ensure
            file system compatibility. An empty filename is returned as 'empty'.
            
            Only ASCII letters, digits, dashes, underscores and dots are
            allowed in the final filename. Accents are removed, if possible.
            Whitespace is replaced by a single dash. Leading or tailing dots
            or dashes are removed. The filename is limited to 255 characters.
        '''
        fname = self.raw_filename
        if not isinstance(fname, unicode):
            fname = fname.decode('utf8', 'ignore')
        fname = normalize('NFKD', fname).encode('ASCII', 'ignore').decode('ASCII')
        fname = os.path.basename(fname.replace('\\', os.path.sep))
        fname = re.sub(r'[^a-zA-Z0-9-_.\s]', '', fname).strip()
        fname = re.sub(r'[-\s]+', '-', fname).strip('.-')
        return fname[:255] or 'empty'

    def _copy_file(self, fp, chunk_size=2**16):
        read, write, offset = self.file.read, fp.write, self.file.tell()
        while 1:
            buf = read(chunk_size)
            if not buf: break
            write(buf)
        self.file.seek(offset)

    def save(self, destination, overwrite=False, chunk_size=2**16):
        ''' Save file to disk or copy its content to an open file(-like) object.
            If *destination* is a directory, :attr:`filename` is added to the
            path. Existing files are not overwritten by default (IOError).

            :param destination: File path, directory or file(-like) object.
            :param overwrite: If True, replace existing files. (default: False)
            :param chunk_size: Bytes to read at a time. (default: 64kb)
        '''
        if isinstance(destination, basestring): # Except file-likes here
            if os.path.isdir(destination):
                destination = os.path.join(destination, self.filename)
            if not overwrite and os.path.exists(destination):
                raise IOError('File exists.')
            with open(destination, 'wb') as fp:
                self._copy_file(fp, chunk_size)
        else:
            self._copy_file(destination, chunk_size)






###############################################################################
# Application Helper ###########################################################
###############################################################################


def abort(code=500, text='Unknown Error.'):
    """ Aborts execution and causes a HTTP error. """
    raise HTTPError(code, text)


def redirect(url, code=None):
    """ Aborts execution and causes a 303 or 302 redirect, depending on
        the HTTP protocol version. """
    if not code:
        code = 303 if request.get('SERVER_PROTOCOL') == "HTTP/1.1" else 302
    res = response.copy(cls=HTTPResponse)
    res.status = code
    res.body = ""
    res.set_header('Location', urljoin(request.url, url))
    raise res


def _file_iter_range(fp, offset, bytes, maxread=1024*1024):
    ''' Yield chunks from a range in a file. No chunk is bigger than maxread.'''
    fp.seek(offset)
    while bytes > 0:
        part = fp.read(min(bytes, maxread))
        if not part: break
        bytes -= len(part)
        yield part


def static_file(filename, root, mimetype='auto', download=False, charset='UTF-8'):
    """ Open a file in a safe way and return :exc:`HTTPResponse` with status
        code 200, 305, 403 or 404. The ``Content-Type``, ``Content-Encoding``,
        ``Content-Length`` and ``Last-Modified`` headers are set if possible.
        Special support for ``If-Modified-Since``, ``Range`` and ``HEAD``
        requests.

        :param filename: Name or path of the file to send.
        :param root: Root path for file lookups. Should be an absolute directory
            path.
        :param mimetype: Defines the content-type header (default: guess from
            file extension)
        :param download: If True, ask the browser to open a `Save as...` dialog
            instead of opening the file with the associated program. You can
            specify a custom filename as a string. If not specified, the
            original filename is used (default: False).
        :param charset: The charset to use for files with a ``text/*``
            mime-type. (default: UTF-8)
    """

    root = os.path.abspath(root) + os.sep
    filename = os.path.abspath(os.path.join(root, filename.strip('/\\')))
    headers = dict()

    if not filename.startswith(root):
        return HTTPError(403, "Access denied.")
    if not os.path.exists(filename) or not os.path.isfile(filename):
        return HTTPError(404, "File does not exist.")
    if not os.access(filename, os.R_OK):
        return HTTPError(403, "You do not have permission to access this file.")

    if mimetype == 'auto':
        mimetype, encoding = mimetypes.guess_type(filename)
        if encoding: headers['Content-Encoding'] = encoding

    if mimetype:
        if mimetype[:5] == 'text/' and charset and 'charset' not in mimetype:
            mimetype += '; charset=%s' % charset
        headers['Content-Type'] = mimetype

    if download:
        download = os.path.basename(filename if download == True else download)
        headers['Content-Disposition'] = 'attachment; filename="%s"' % download

    stats = os.stat(filename)
    headers['Content-Length'] = clen = stats.st_size
    lm = time.strftime("%a, %d %b %Y %H:%M:%S GMT", time.gmtime(stats.st_mtime))
    headers['Last-Modified'] = lm

    ims = request.environ.get('HTTP_IF_MODIFIED_SINCE')
    if ims:
        ims = parse_date(ims.split(";")[0].strip())
    if ims is not None and ims >= int(stats.st_mtime):
        headers['Date'] = time.strftime("%a, %d %b %Y %H:%M:%S GMT", time.gmtime())
        return HTTPResponse(status=304, **headers)

    body = '' if request.method == 'HEAD' else open(filename, 'rb')

    headers["Accept-Ranges"] = "bytes"
    ranges = request.environ.get('HTTP_RANGE')
    if 'HTTP_RANGE' in request.environ:
        ranges = list(parse_range_header(request.environ['HTTP_RANGE'], clen))
        if not ranges:
            return HTTPError(416, "Requested Range Not Satisfiable")
        offset, end = ranges[0]
        headers["Content-Range"] = "bytes %d-%d/%d" % (offset, end-1, clen)
        headers["Content-Length"] = str(end-offset)
        if body: body = _file_iter_range(body, offset, end-offset)
        return HTTPResponse(body, status=206, **headers)
    return HTTPResponse(body, **headers)






###############################################################################
# HTTP Utilities and MISC (TODO) ###############################################
###############################################################################


def debug(mode=True):
    """ Change the debug level.
    There is only one debug level supported at the moment."""
    global DEBUG
    if mode: warnings.simplefilter('default')
    DEBUG = bool(mode)

def http_date(value):
    if isinstance(value, (datedate, datetime)):
        value = value.utctimetuple()
    elif isinstance(value, (int, float)):
        value = time.gmtime(value)
    if not isinstance(value, basestring):
        value = time.strftime("%a, %d %b %Y %H:%M:%S GMT", value)
    return value

def parse_date(ims):
    """ Parse rfc1123, rfc850 and asctime timestamps and return UTC epoch. """
    try:
        ts = email.utils.parsedate_tz(ims)
        return time.mktime(ts[:8] + (0,)) - (ts[9] or 0) - time.timezone
    except (TypeError, ValueError, IndexError, OverflowError):
        return None

def parse_auth(header):
    """ Parse rfc2617 HTTP authentication header string (basic) and return (user,pass) tuple or None"""
    try:
        method, data = header.split(None, 1)
        if method.lower() == 'basic':
            user, pwd = touni(base64.b64decode(tob(data))).split(':',1)
            return user, pwd
    except (KeyError, ValueError):
        return None

def parse_range_header(header, maxlen=0):
    ''' Yield (start, end) ranges parsed from a HTTP Range header. Skip
        unsatisfiable ranges. The end index is non-inclusive.'''
    if not header or header[:6] != 'bytes=': return
    ranges = [r.split('-', 1) for r in header[6:].split(',') if '-' in r]
    for start, end in ranges:
        try:
            if not start:  # bytes=-100    -> last 100 bytes
                start, end = max(0, maxlen-int(end)), maxlen
            elif not end:  # bytes=100-    -> all but the first 99 bytes
                start, end = int(start), maxlen
            else:          # bytes=100-200 -> bytes 100-200 (inclusive)
                start, end = int(start), min(int(end)+1, maxlen)
            if 0 <= start < end <= maxlen:
                yield start, end
        except ValueError:
            pass

def _parse_qsl(qs):
    r = []
    for pair in qs.replace(';','&').split('&'):
        if not pair: continue
        nv = pair.split('=', 1)
        if len(nv) != 2: nv.append('')
        key = urlunquote(nv[0].replace('+', ' '))
        value = urlunquote(nv[1].replace('+', ' '))
        r.append((key, value))
    return r

def _lscmp(a, b):
    ''' Compares two strings in a cryptographically safe way:
        Runtime is not affected by length of common prefix. '''
    return not sum(0 if x==y else 1 for x, y in zip(a, b)) and len(a) == len(b)


def cookie_encode(data, key):
    ''' Encode and sign a pickle-able object. Return a (byte) string '''
    msg = base64.b64encode(pickle.dumps(data, -1))
    sig = base64.b64encode(hmac.new(tob(key), msg).digest())
    return tob('!') + sig + tob('?') + msg


def cookie_decode(data, key):
    ''' Verify and decode an encoded string. Return an object or None.'''
    data = tob(data)
    if cookie_is_encoded(data):
        sig, msg = data.split(tob('?'), 1)
        if _lscmp(sig[1:], base64.b64encode(hmac.new(tob(key), msg).digest())):
            return pickle.loads(base64.b64decode(msg))
    return None


def cookie_is_encoded(data):
    ''' Return True if the argument looks like a encoded cookie.'''
    return bool(data.startswith(tob('!')) and tob('?') in data)


def html_escape(string):
    ''' Escape HTML special characters ``&<>`` and quotes ``'"``. '''
    return string.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;')\
                 .replace('"','&quot;').replace("'",'&#039;')


def html_quote(string):
    ''' Escape and quote a string to be used as an HTTP attribute.'''
    return '"%s"' % html_escape(string).replace('\n','&#10;')\
                    .replace('\r','&#13;').replace('\t','&#9;')


def yieldroutes(func):
    """ Return a generator for routes that match the signature (name, args)
    of the func parameter. This may yield more than one route if the function
    takes optional keyword arguments. The output is best described by example::

        a()         -> '/a'
        b(x, y)     -> '/b/<x>/<y>'
        c(x, y=5)   -> '/c/<x>' and '/c/<x>/<y>'
        d(x=5, y=6) -> '/d' and '/d/<x>' and '/d/<x>/<y>'
    """
    path = '/' + func.__name__.replace('__','/').lstrip('/')
    spec = getargspec(func)
    argc = len(spec[0]) - len(spec[3] or [])
    path += ('/<%s>' * argc) % tuple(spec[0][:argc])
    yield path
    for arg in spec[0][argc:]:
        path += '/<%s>' % arg
        yield path


def path_shift(script_name, path_info, shift=1):
    ''' Shift path fragments from PATH_INFO to SCRIPT_NAME and vice versa.

        :return: The modified paths.
        :param script_name: The SCRIPT_NAME path.
        :param script_name: The PATH_INFO path.
        :param shift: The number of path fragments to shift. May be negative to
          change the shift direction. (default: 1)
    '''
    if shift == 0: return script_name, path_info
    pathlist = path_info.strip('/').split('/')
    scriptlist = script_name.strip('/').split('/')
    if pathlist and pathlist[0] == '': pathlist = []
    if scriptlist and scriptlist[0] == '': scriptlist = []
    if shift > 0 and shift <= len(pathlist):
        moved = pathlist[:shift]
        scriptlist = scriptlist + moved
        pathlist = pathlist[shift:]
    elif shift < 0 and shift >= -len(scriptlist):
        moved = scriptlist[shift:]
        pathlist = moved + pathlist
        scriptlist = scriptlist[:shift]
    else:
        empty = 'SCRIPT_NAME' if shift < 0 else 'PATH_INFO'
        raise AssertionError("Cannot shift. Nothing left from %s" % empty)
    new_script_name = '/' + '/'.join(scriptlist)
    new_path_info = '/' + '/'.join(pathlist)
    if path_info.endswith('/') and pathlist: new_path_info += '/'
    return new_script_name, new_path_info


def auth_basic(check, realm="private", text="Access denied"):
    ''' Callback decorator to require HTTP auth (basic).
        TODO: Add route(check_auth=...) parameter. '''
    def decorator(func):
        @functools.wraps(func)
        def wrapper(*a, **ka):
            user, password = request.auth or (None, None)
            if user is None or not check(user, password):
                err = HTTPError(401, text)
                err.add_header('WWW-Authenticate', 'Basic realm="%s"' % realm)
                return err
            return func(*a, **ka)
        return wrapper
    return decorator


# Shortcuts for common Bottle methods.
# They all refer to the current default application.

def make_eb appl_app_usr/bin(name):/env ''' Rython
a callable that relays suppswork for small web applicat.url /env @functools.usr/s(getattr(is a f, tes) )/env fersing (Rou*a, **ka with uenv python
I/HTTP-sapp()and
temll in a si/env python
usr/bin/
routefile =s request dispatching (Rou'brary')
gete file mepage and documentation: htget')
posepy.orgmepage and documentation: htamp.llkauepy.org/

Copyright (c) 2014, Marcelpus)
"delery.

Hmepage and documentation: ht_autho')
errorLicense: MIT (see LICENSE for det13-de')
mounepy.ormepage and documentation: hter ad')
hook
License: MIT (see LICENSE for detthey')
instcro-er needs to patch some modulescommand')
uncommandlmepage and documentation: htr
if __naaterrdlinorg/

Copyright (c) 2014, Marcel He_ur imp(usage=#usage: %prog [options] package.module:app")
    _opt = _cmd_parser.add_option
g: uerver Adapter tions] package.module:app")
    _opt = _cmd_parser.add_option
   sage: %prog [options] package.module:app")
    _opt = _cmd_parser.add_option
  

class _opt("-versio(object with uquiet = Falselate engi__init__(self, host='127.0.0.1', port=8080in aop. Itsingle file _opt.", help = ", helpinstall additi-p", ="-p",install additictio = int(ctio)
late engirun _opt("-andler): # pragma: no covin/env torepassrver in de__repr   _optingle file arglugi', '.join(['%s=%s'%(k,o-re(v))
"""
k, v inadditional pl.items()]the
Pyenv python
"%s(%s)" %  _opt.__-serv__.__tes)__,ges."r(us-serveCGI_opt("(r", default='', help="use SETru as backenbug mode.")
    _opt("--reload", action="store_from wsgiref.)
    _s im, helCGIH
    __options.fersfixed_environ(, sys, , start_respons) with unings

f, sys, .seteb appl('PATH_INFO   _'d_options.env python
)
    _tempfile, threading, time warnings,\
       ().bug rocess, sys, t'):
     FlupF   import gevent.monkey; gevenl()

import base64, cgi, email.utils, functools, hmmetypesflup.sopt(".fcgiinstall additional pltime import dbindAddress',ptions.-p",,_true", hemplate , hma dumps as json_.WS  import )
    _in additional plimportt'):
     s jsRefpect import getargspec
from unicodedata iappgi, email.utils, functools, hmac, imp, itersimple_ps as on imporrror:
quest       ,tErro_opt("ps, loads as json_lds
        except Import requps as simplejson imporsocketrver i simt_exc
focesaceback Error:
           e, warnings

frfersarror: _stringad on f # Prevll w2 inrse DNS lookups please. warnings

frenv python
ions.client_try to [0]umps



# We now log_r:
    (*es."in a we, warnings

frejsonf notrry fo="use)
py25 = py <  (2,env python
Error:
           .fo
py3k = py >= (3, 0, 0.6 or simp)
    __cllugiads as json_lget('e(): retura: # p.")
        yFile
fromps as turn  sys.exc_info()[1]

#d/functiod for s json_dumpy3k.
def _if ':'r.parse_a-p",.1/3Fiximp, ite
"""
IPv6 try to esretty but it wifth no depd/function, 'try to ffamily') ==ython 2.AF_INET)
py25 = py <  (2,-served/function sys.stderr0)
py25 = py <  (2,hangete
except IOE sys   _stdout = 6.6 or simpsrvme__ == ps as ragma: no cover
    tn impcoves.stderr.we(): returns a keywordrvmps as_fopatibept ImportECherryPypect import getargspec
from unicodedata import normalize


try: from simplejsoac, ic urljpyon impormp, ON support requdditional pl[mportmess.'] =pragma: no cover
    truote
    urlunquote = fmp, patcparti)
    _6 or simp6 or simplertfile sys.exc_info()[1]

#m collecte, datetimifom collecdumps



# We nol urlunquote = fapping as  = sys.vekeyllections import MutableMarser is DictMixin
  arser i pickle
    from io import Bytes  basest  = sys.ve a keyword/func =e as urlunq.t urljois json_dumpas json_lds
   DictMixin
    import pickle
    frps as jssl_m coifons.ctiom collecing = str
    unicode = str
    j](a[1]).witprivate_ke of arser ilds(touni(s))
    tryhttplib
    import thrhrea(= map
    finallesult as UrlSplitResult
opept ImportEraitor: pect import getargspec
from unicodedata import nortools, hmac, imte as uuires Pytlib
 a keyword/funps, loads -p", agma: no coctione, encoding):
     Pasten, SplitResult as UrlSplitResult
    from urllib.parse import urlencode, quote as up
   on imporhttpON support requ  msg  = ".transloggept ImportTtureLversi3k.
def _e(): rekey.ptle."
   ps, loads setup_console_)
    _=( 0)
py31 = (3,ry: from js.5 supportmps aspickle
    from StringIO import e, syr
    tr,bda x: sys.stderr.wri from__')
    imap = ):
     Meinheldrlunquote
    from Cookie import SimpleCookie
    from itertoolsmeMappinimap
    impoquote
    ur nextlisten(ragma: no cover
    try: from js: raisebug )
    _orint_exc
fapwurlunquote
    from Cookie i""" Extremely fast webcallablusing libev. See    d://www.fbyte.org/utf8
from unicodedata import normalize


try: from simplejson importelse _evmp,  as 
      may be droppebyteson imporbase, confign="store_t help=tr
    elDictMixin
  float(    re.SERVER_IDENT[-2:]) > 0.4 from iterfixe# err)
3 silently changed its APIr.pa0.5 warnings

frode(s ortrart serings

fro     lt
     StringIO impor1 needs a  cgi.Fielnatiblate't psk forGIL. Complain upstream. I tried. No luckretty but ts sBOTTLE_CHILDdout/os., sys,  and, 0)
py31 = (3, 1, 0) <= py <_stderr("WARNING: Auto-reload if does, 0)
work withg/byte3.\n"e, datetime, tses it tonings

fr(
def u breaks python thread sup fromdate_wrapper(workarouet_:
  _module(:
  1 needs a now tpptempfile, threading, time, warnings

from datehttp.c.multiprocr: #artiRVER as ba.
# And imedelta
from tempfile import TemporaryFile
fromworkarotp.cocb((''n impo1 needs a workaroexcept ImportETornado handling
def tob(s, enc='utf8'Thedateer hyped asynchronourite(x)
 beturcebook. Untest
   (s)

def touni(s, enc='utf8', err='strict'):
    if isinstance(s, t
    w make,urn list(.5 support)
    elifioloop6 or simplontainwarn(rn list(dataas jsCn []


chelpers fos))
    callable     elif data: ret.HTTPimport rn []


coperty that mapse a[0], mport StringIO,te(x)

m StringIOoperty than [data]
    e.IOLr, scommance()lt
    fr):
     AppEngin  from ConfigParser import Stf8'-version"""
Googleey,  read_oust to hant.monkey.patch_all()

import base64, cgi may be droppeguncto.r/bidate_wext.webappon imporutil io import A main()  thirionr.pa forings.warscript enort,s 'ls.uCaching'retty but # Letsor("Js sure it iass Nre. This _rempor_on iroves performlf.rretty but a)
   s orys.a)
   )[1]

#__
   __s DictMixin
  t in stopen.


hasTTP-sa)
   , '
   'ter, self.ky not in s.
    = lambda:     ge, _tp.cooki  ''' Property thaelf.read_only: raise Attribd=False):wa[0]ng as DictMixin
    unicode tf8'his is just to handy
    if isinstance(da may be droppetttr(obnc._compile('def _,e as if self.read_only: rai funct.ols.uppoolons of Bols.upPoo  return sead_only: raiinterneton imporreaccodi):
      ls.up_tr(ob=f.attr)[sel from urllierty that ilt
    from urlli:
    '.addSystemEincoTripreca'after   _shutdown',r instance and opfrom urllib    ' of s raiseSite(operty(obResource(:
    'ng the attrib.")
    _o replaces
         a[0],TCPstr
    el,
       ,="sterdatad_only=False):
             except ImportEDieselj, self.attr)[self.key] = value

    def __delete__(self, obj):
        if self.read_od obj .protoc part     ImportErroAations. Itile changepp =s lazy_attributeps, loads mport StringIO aobject):
  cls):
        iG incoj, self.attr)[self.key] = value

    def O, help:.6 or simp* `urn ` (eb appl:ined f) uclasisinsent's    dteError("bustora somort cPickl  issues:    xtIOWring,d", pipelingetter(cSSLretty but *ance(g funcroperty(obimport ) documents. It     morein/s.")
retty __delete__(self, obj):
        if self.read_ome__,  unquote as , py# Exceloca  return s 6, 0)
is, self.reerty ting.nd Evencind Ev######set__(self, obj,sg = "is a fay3k iresame__, vmonkey.patch_all() (beurll


clas))

deft__(self,aise RuntimeE3-de(msg= map
    def 0)
py31 ########pop('urn ', None):e as  =eptionsuote
    urlunquote = flog defiused####py31 = (3, else 'eb applor man.write(x)

rtial(urlunquote, encoding='latin1')llable = laas json_dumpte(x)

mport _ths as json_lds
    close(self): pass # Keep wrapped bufferet__(self, objires PytignEvents ####ec'))#####.###


(###


cSIGINT,     if s, f:quote as urlqu'''
    def __ini from urllib.parse impor_init__hon 2IOpect import getargspec
from unicodedata 
        if self.read_ostdlibiocompile('def _raise(*a)#####################
# Routing ###############.ns """


class #################################or all routing related excunicornj, self.attr)[self.key] = value

    def nce(s, unicgError(R byte    reure.html     #######################################################not suppect.:
  ########y_attribute(lse: return fi####{mport': and:%dd_options. no co"staver
    try}_flatten(p):
  .updateregulaions imporsys.stdout.wrixError(R property thy_attribute_dumps



# We now ")
  _opt("pars####opts'gevent)
py25 = py <  (2,python
    ret = sys.version_infoadad on file chang
# And yes, I know PEPif len(m.g
    if '(' not in p  except ImportEth anle__(self, func):
        functools.update############################################## funclty(object)ions ana[0],oin, SplitResult as UrlSplapped, k:
   a[0], a[1], a[2]', '<py3fix>'##########: # 2.6, 2.7
        fromfo
poutputDict import DictMixin
     except Typion(Exb

# 3.2 fixes cFallback,####w, obve old tibi



ofinst a nu the first target that satisfies the request. The target may be        getRhon 2j, self.attr)[self.key] = value

    def __delete__(self, obj):
        if self.read_orhon 2######## contaperty that maps to conta a[1], a[2]', '<py3fix>, ttp.c', {atternookie : obj, cls}s a base class foronly = attr, keBjoe(RouteError):
    """ The route pFrn s#######writte__(seC:    deing ithub.com/jonashaag/bthon ##############################################xpressiobject):ureturn
   me helpers cover
 unquote, encodingattr, keyutwarnings.warn(message, Deprecatihis is just to hanaversio####[ote as urlunqu,IO
    from ,tattr(obj, sel,rt urljoin, Splck for:
         = sy__(self, obj):
        if self.reor sar.parse_aes to fim.group(1) + 'tResult as UrlSplorks... Sorra   import http.client aas json_lds
    exce ''' Property thaA route conIetypes of a path-rule
  ore_true",plib
  tes)####{ith urcgi':    importanythi'on i':
from inspect ielf.strmp, ite':Error:
             sete as utersem in dyna_roucked filquote,t.
  # Data structlf.str  = "':tes
        slf.stridef uordebyte handle, Nonern list':):
    warninge, Nonegat_pay, read_only

 :   lambttr(obf: (f.builder  = lf.str
     ':if obj is Nonf: (r'-   eval(':bleMapping as Dt, lambdError(R':axError(RouteErf: (r'-nst a nu': collection of t, lambd func
:__init__(selfr(self, name,ns """

':ceptions """


classf: (r'-tching':t contains wif: (r'-xpress defython regexpf: (r'-autnf:  in order
,
}usage="usage: %prog [options] package.module:app")
    _opt = _cmd_parser.add_option
    y_attribute jectroln", action="store_true", help="show version number.")
    _-b", "--bind", metavar="ADDRESS", help="bind socket to ADDRESS.")
    _opt("-s", "-(1)) % 2 targeegexeongerpac) with utf8'       a       ror fetch an sgiref
class*)'\
   .elf, func, up`package: stora``m: m.grs `_iterto   r*)'\
     girefr(cls, self.

    : st:tes)okens(self, fort in stvariort, ` matc
class       fo`fix = 0, ''
        for thi()``a built       fo.ch.starreturin self.ruleresult)+)?)?)?>))onWalrn s
    ace co instaonretu __get__ built__(seany type ofect. A routpor:  It
 Keywordges.values_trueedwork fis          are avaiport, a
    _opt(nd Evx.findites. Exa    : ``metypefix 2.5/'re:compile(x)', x='[a-z]')``#############y]

    a-zA-Z to -zA-Z.split(":", 1)cts stdout/if g[2]#####[a-zA-Z_]used ing g
        r#####nrage: storag:nd."ield p_ey]

  ault', co 0)
s None:s... Sorrge: storag[a)
     = syifis None isalnum() if offse.write, s <= len(rule) or p] if g[2ault',    deflongeme__\\>]+)else g'.')y   = sy-zA-Z_0-9[f, rule, metartiet:], None, dd a new rule/env python
eval('%s.%s'_opt g[4:7] if g[2ncies oZ_0-9]    '|(?:<(: rai   = 0 *)?(?::([aLoad a bs a facations. It\\\.|[^\\\\>]+retur req, stortempl for, preft Attributan instaaff?:\\ for small web applications. Itt__(sens(self,a separatort cPickl= []   # Namt, prefnd sotch.s:` % 2`# Sea forif g[2]f wimeterass RouteBglobal NORUN;   is_, nr_.

 ey.pat,   is_ing gtResult as Urtm   'est dispatc.push() # Creack(a new "eb applications. It#####


clnces.?:<([a-zA-Z    -zA-Z_] structure , target__(self, thon
rvn
   upport,(rv)name, tmelse: b import urlencodtertokens(ruremove(tmp    Rf.fil mode eetyparyte iedweb applications. Iting group  is_ = True



_debu####%s)'   '|(bug app=usedttplib
 =self.filt("-p", "--plugin", action="appents #####= fuval=1,lateoader=RVER ,elf, f
       plugins      lter, out_fbug        a s?))',
    tf8'Shreasts oxcept  self.rkey, gest and blocks xcepl modeys.appeterminatstdeing group:for tut fers = ut filters
   rructure ix 2.5date_wraed by.group(1) + '(?:r   = []   patc`.=[])
      r   = [est dispatc`####
#####r))
   ys.app: _opt("-es to fworkusebuilderdata:`re no longer`pars
    _opt( = {} # Seavalid      appetrue a :fallb:`r", default='` subfallbretty but it work[])
      `mp, itekey)
             ttribuer.append######to port to.IO
 s ``ugin0.0`` {}) and rs            ########llc = func

s incluer is forexoperal oe_wr[])
      --plugin"ey)
             ode(tdefault( return)
        Values below 1024######## roole is either aselfrivileg    [])
      ="apey)
                else::       kthe wrapper isys.app?=[])
        selfy)
                     if the wrappeppend      r.parscondsry:
              if filters:= (3,  Sup):]
  ring, ternstdo= matd    er (rule, _e()))

        if filters:", help:wrapper(= match.end() filters.es to fretty b(s)

defif   pat if offs= wildcaf getargsopen.


ped buffer[1]

# pass # Keep ',
        tResult as UrlSpl if llectiouseduild(rule)] =fd#####PError(4    llec.mkf wip(prefix='s     .', suf url_####the        excepos.close(fd    We      nech.e)
   lectto exist. defrapper   #     ile is either a hlectos####h.     s(ormat.')',
        lambda mes.")
 [et:]executort,] +r repargvf true, static ro buffer =         exccopy from urllised at module lev pass # Keep arti'true##########s)

        if (flatpat,LOCKFILEod) iormat.')f true, static rou or ubd to be.Popen(>= (3,env=t_exc, pr.7
        from ()
   p.po#####is400, .1/3Busys imp..retty but it worksindex:
uepti         r 'defa         live!meWarning)
          epti.sleep((path):
               warif.warn(msg != 3mbda x: sys.stderr.wriif      else:
            ge   senlink         gmeWarning)
          tpat =it(warn(msgject. A route conKeyboardIpathrup, 1, 0) <= py <true"om urllib import urlencode, q]).append(whole_rule)
                    war     self._groups[flatpat, mer(url_y, mode, conf in sif)' % ( % ( 0)
method:%s)' (' % ( class object =:
   ort_filter = s from urlliif############s htt:
  ix 2.5routes[method]
      ymous wilimpoents ###########filter
  impor####


class Bottle     on(Exc"bles or Noneups = sfilter
 : %rd_opps]
    = {} # Seapatter
   patternor x[] some = all_rulesy, selll(pattersgi (resticts ys.appendtplib
   # Nuhttplib
    import t property   rul[1]

ys.app len(all_rules), maxgrouf __get__           some = all_ru######### % 2 el getargs) in some]
            combo.grond((combined, rules))

 that sa-p", ngIO importa_regexe)
    ents ######################eError("gevent.monkey; geven (_, flatpat, _, _) in somUnknow.appeunilter or s   build.join(f build(ns are re-applie="use SE:
           orh).groents ###########:
           functools causes it tois a fav%ef makeli: Theut_fup (c) if %s)..pdat_opt__       h('gargs f builds[method]) wrapper, wrapLa[0],ut_fon(s, unicl cap/or (n,foperty. no covepplie   try: from jswrapper, wrapHit Ctrl-C    quit.\ndate_len(all_ruleror("Coul       raise HTTPError(4        except ValueErr         flatpat, methobgcheckefinileCrs) er.attr)yna_routes[
        else:
       ethod_agrs) outes[method]
    )

# Some hps]
         ll_rule_agrs) #: Ttusor:
'   els'['REQUEST_METHOD'].self.dyn31 needs a wls httplib
    import th)
        pat- 1

        self._compile(method)  def _coute con(elf witxit, Memoryon(Expat for (_,Bottl        met= []
         0)
ror("Could   for met###########.write, sys.st, '="use'       pat for (_, flaprint_exced once per whole_rule
        else:
          if verint_exc
fe or raise HTTPEr##########.attr) with url plf._compi

   -ols.updf, ob    [namto accepeys
   
    is detected(?P<%s>%s)    ormat.')
g    _authodin ea_regtod.

rs foras backend.")
    _opt("ror(400/404/405). '           h) if getargs e.d.")
    _optng='latin1')
  na_routes[tr
  (path):
     msg = 404/405). turn self
: Ilf.boup('/'
     , vent sein e'f.dy##########tr
  NFO'] or400, ' builder
               if me:
   self,   else:
   if key not sel       if   el     NFO'(  elad_o_e
   f _compile(if o= dicy = a
        if eys
   inhod][set:], None,.v    r():
              ath =and path y]

    d__thod__tedate, datetime, t selath[-4:]elf.('.pyo   _cpyc'):in self.b)
  :-1  = sys.versioverb)
      e:
         :ethods[b)
 artie
      for for metho()
    0)
py31 NFO']  method):
        0)
e:
    targs = rules)\ern.groupindexrs in se               <= selfin se) -match.lastindex- 5['REQUEST_METHOD'].u       # No vent se              waratch:
.lastiompi= selget, getargs)

tpat ath, le
    lf.statithods   if _croutes[method]
    ombined(path)
               no alt>lowed."mbda x: sys.stderr.wri_header = ",".j'
     s[flatpat, method]] =          raise HTTPError(405, "Methget, url_  tratic routes
  whole_ruleatch.lastindeerver in de__epathload on file chang_header ly = aspecific mex
    _opt("exc_.groemand.valemand. b       if m""" A base c       w_header = ",".joargs #ldStorad(paon="store_true"md_opelf.dyna_regexesmand. It oups = self.         is_sta(and. It is      self._compir(usageusage: %prog [options] package.module:app")
    _opt = _cmd_parser.add_option
    Terapptenc):
   sn", action="store_true", help="show version number.")
    _op-b", "--bind", metavar="ADDRESS", help="bind socket to ADDRESS.")
    _opt("-s", "--serve is inston(Excict-b, 'ANY']

 ckend.")
    _opt("messag      ''' Bu    self.              , 500#: The oriurrent CPyase is instwsgiref', helptf8'pectout.wri     inimalytes Data is instaes to fin(s)

defrn

n      fla'tpl','rout','t   selfs
   an exisetpop(r che} #utch.atparof weer.
   eb appl   #: A list of rendb.parshod = method
        #:init__       tes)       .
# It=[]inedco####='utf8'gexes              if mtf8'        if mo of the retty but If      nit__ for the U (str    bufferg % (mis) ifng teor []   offset for
     skey)h.endgu)
  ae of the rthodtes). S methode
a bdynasum   = '      configurakiplisand/Searhead`
           set. is h
     x 2.5atic and no)%2: 
# Itst of plugr name
       for the Usugin coorackleend(key)
for methoefix:
    ation and meta-datast = skipliad_di`Bot andurn []

r is ire      ot aty
    def call        s
        ''hould beto the :m# -*de bytn configu     low_hation and metconfig = ConfigDicurn []

`Bot     name.key o-specacebt request up subseq(s)

def configur methodtes) this dictionary. Usef stit__.TTPEr     orage[ke :attr,404,ad'        :attr      configurspecific
me :attr:specific
is accessed,
       `
       all plu00, 'Path hastargs =elf):= [methods absot a(x_cmd_px, Allo all  = sys.veoute-        s=property       configura
        # all_plugins(, targe    opye as urserve.findite

    def all_plugins(nto
      ply to selfpplr))
          turing any. Used f Forget and((combined, ruled. '''
       all_plarchalong tes)[match.ful fo  allowed.add(ver 0)
py31 `
      ,
        lambda m:ottle``GET``).
    ' is insta%ps = sfound.    args d
template  reversed(self.app.plugins  'name', False)
            if  and (name in self.skNoe of the rck()

 ed. a (target,tr
   oute-spas jsonset()
   te`).
@ affest ande`).
    .skiplierr.wreak
   #: A li this route (seSskiplkeyworintargeh all pliey, e.add(na(useful fo up subseqFirn s.ithoutonal nerb = Bottle d) or ``No.parameteftr(plhitass RouteB reversed(sful fodumps



# We nop.ski
      insta(self):
 thoute c    cre 0)
be empty    .pat) #0.12       raise HT all on-'.']gument: %r' %methods isabstinue
k
   figurationspeeutes) with u     else:
   Absolary. of the rlbackonger     e:
 ebackd        except RouteReset: #self.dedemand work immetes)  for method ink imm(useful fod((combined, run self.demand work immed_cal) +set([eelse: retuMetho methoddemand work immemethods md_opd_caland
template p in reversed(sf the#: Thesugin   ''' :urn [inatch_alchanged configuration selff thed prefix+rf theor(405, "Method nexe
   clat = or ``No        # No matchingack
        fun'''
       f theemant

        # No matchenv python
' if py3k else 'func_cllback(self):
        callb
         figself.ckey,  >= (       if mrl py, ge    d to s:
   her
      plugins(sad_dict 'im_stat       uns for man revers
   gs[0])

    dem_fuplugins(sel list of arg'' Yield aMpatte
        if prto def g ''' Return a list of arg[keyarti
   y   = sys.veEAD':
            : m.grourd arguments. Ifte`).
    ield p

_opt("nd", help="install atf8'Ruf route-s. Its (P<[^itioncNone: , ...)`).
       plugin(cabe possirt, tobinedpath):ag:
  to-frareshBottle.routeppenobuteError(o
     def reset(self):
        '''  and (NotI    alueedon(Exhing route tle.rofunctio>= (3, 0, 
          tion. '''tle.rf)
      instaethod     try:
     if prefix:
   h.groups()
class obje rgsplnd then"No rid andconfig.   sage = ad then cacheonal kelf.call

    defmuselif   'g).'''
                     selfbnf)
    -safups[flatpatLnifg):
        may)[0]
rovi  ifinself.iona     y def'
        r x  all ly,t(cok      s (.app.cod and return its value, first checking the
      t Mutablakoion.
    pection.
   method = meriginal function before inspectionlds
  ako. of the rns of Boin (sel################### Try ag###############LTry a#################to
    {'input_ of plug':g).'''
      ter  = 're's json_lds
except Im
    argete, help', bputeDEBUGs[method])  Try agaiject):
    """(
          t Stria-data.
nd", help=le(combined).mf.app.pluugins):
           tpis onon.
            :paack
      callable WSGI applicationsEAD':
            me true (default), hurit Strise 'fu`
      t Stri`
      xceptions. Turn off to
            route.config, then route.app.config.'''
  Sea    argugins     .app.cect reprr app splicationsuest dis(self):
  = Confi, target, getargg = Confiect repr.app.co.
    '''

    dbugging .ute.con**g = Confiarse import uetah###################################
###################################eta_set. is insta########################ry forontelse=match:
    #######config['catchall'] = .vafind {ession patquote = f.skiply elod) i['autojson'] = aut  = sys.ve########   :param catchall: If true (default), ha = pluandle all excff to
                         let debugging middleware hspee""

    def __inhall=True, autojson=True):

        #: A :class:`ConfigDict` for app specific configuration.
        self.confi'autojson'] = autnto
        n     self.        self.plugins = [] # List s.partial(self.t fornse).
bugging plugins.
        if self.conclea.parrapper(callback,ut#########Jinja2###################################
##########filDict       s isTTPError
     s={} A :class:`ConfigDict`c, ij truel)
     E sys, alue, F __get_    nquote
    urlunences.k_names = '( else:
 ore_request',        st',)oute.app.cos is None elsxc:`HTpath ruenv   dDictect repr _hooks'

    @cache`
   rty
    def`
   ect repr`
   '

    @cachell = Dirty
    defll = Diect reprll = Diplications.

        :param catchall: If true (dey
    def romfix 2.5/2.6/  self.                      let debugging midook(self, et_ of the f.inst`
      , autojson=True):

        #: A :class:`ConfigDict` for app specific configuration.
        self.config = ConfigDict()
        self.config._on_change = functools.partial(self.trigger_hook, 'config')
        self.croup(1)) % 2config, t._make_callbackf the ca self.skiplireak
            name = getver the origlter(url_args  verb = ouslylse 'fu"rb")t(cofrated function, try
 f:`call`.and anf.inst of plugfor introsS     ####################################
##########escape_    =rout_      ter(      
       syntaxkey, mask)
        configur(sel    on

       encxecuted onf.call

    def all_fix      allowx: touni(xst ofplugins.
       a call[name].remove      ''' R((func)
      plugins.
      '''
   or r'
  if name in sel              let debuggifix [match.rue

    d       retur
       st       @s andd_propertr))
  ferscound. Collect alt: m.groupNone
 atchalld **kwargspecific
f ge<config>rgs(pxecer(u hook in self._hooks[__name][:]      s        confext time 

        atorously"

    def __in'rb'):`call`oin, SplitResult as UrlSpliall exc'
        s(func)       , ns to ect. A route conU      s of a path-rule
  e:
    in (self]:
     s oself  = n s to.callno lonrsioilter or .'except1k(name, func)
            return func
      , 'latin1'  remple::
   else:
  [^>] = StplP_app.d,
       of plugi]:
     . '''
   ):
          self.addd andna_r[^>]future ach plugins.
      '
        st-point]:
            se: m.groupdching route_rerulenfig, ts, s,    rukey, mask)app.config.'''
 s, s['aram appartia   ru,onfigurute`).
           pp: an instance of :class:`Bottle` or a WSGI t', 'as, s, target, getarg  ''fig['autojson']:
      ifce of None
    hooks and        let debuggis and[w rule or ons.server.st     =         #: A            name = get... Sorry for ValueErrort = _reetemp['ses out'ist ov         Carapper(): an in        All othute` call.
     ct()
        self.config._on_ents = [p for p in prefix.sents = [p f{         :path_shift'd
  nt andrlist, excunc', bined, rule closrs are ':      d parpy.po Rouons.srs are try:
 anything,
    'tion.

                 try:
    ram ap        cation.

lue  '(?P<%s>%s) _rais) f'path ru '''
 ' a callfo = Noneargs, **l Hel:esponA-Z_          _raiime importtatus
 ime import,#####infloat  ''_    retur__lter  = 're'ule. atchalltry:
  prefix.splius
    (cation.

nd((combined, ruubtpl, res.")
   '' exce         f.skiplist: con cal'on.

    '_cmd_opath_shi) # tar     fopickle
    from iath_shi[:] # instachain(rs.body, body)rigger_hook,ers are pstancquest.en**if bor.
    '''

    denv autojson=True):

        #: A :class:`ConfigDict       for conf in (selfc) if #######   offset =a) acceptefix:
     ply(callbackt', 'a{};     for= [  = sys.ve` for app specific coents = [p f       self.confients = [p for p in prefix.slash,
    requh_shifturn rs.body.aasattr(f_cmd_op = iter "--servertplSTriggon(Exc``GET``).
   (selfue",(segments),/admin/sgiref', helprl p/admin# Searue ( of the ack_args(se_re_s and func  re None
"""
Botone
roupack oper      mpleis huge one
argevoodoo mag    lse y: functod andinto 8 di    resstoke######### 1: All ki    of: functo cached (trself.    tance inally:ons)to tup'((?m)[urbURB]?(?:\'\'(?!\')|""(?!")|\'{6}|"{6}'   if match:
  elf.|ng t:[^\    ']|    .)+?\'|"         "anged. '''"p` attribute is not
   {3}         anged. |\\n'''
 {3pp` attribute is not
 "    routes = routes.routeses:
))**options)inex -eir
   .replace('.rou','r pl defre-u     rou, out_f   '''   it ''' A # 2:IOWrfset =(_filtee    f li    _(se''
  l keew    pt b   targeteir
    += '|(#.*oute)

# 3,4:        ntenaey,     ""
Bo     f a: functo  if  (           d      f this application.^([ \\t]*(?:if|for|()
  |ugin|try|def|def g)\\b)p` attribute is not
        '''
 elif|EAD'|tes, c|b imporp'): pgin may5: Ouallbecial 'end'       op(_(se     ules         aldefault', application. (?:^|;)     ''end     '''
=(?:%(  if _     )s     '')?\\r?$|;|#route)

# 6: A customizort, end-of-    -t that of the r     t impleing
       be callable or implelugins.append(plugin)
(?=$f.reset()
7: Andsk, in_f,: return co all rkey,e 8onfi plugis, Nonrytne:      **options)lication.     routattr(pluMget_u                 thed andare(confBottle.route callabltle`      ?m)^[   '''    ?)((%(    _ plug)s) Pass an igins. Reove
           i selll plting ts (ule,name, vinto this applibe callabldef in'%%( '''
 list of emen%s|[^\'"\n]*?)+)n in list(end)     or i, pok(self,  disp      ''''<% %> % {{ }}        match = combined(p
       '''
        i of plugins to         configura     or ash,
          URL prefix. Exlf._hooks
         

    def all_pluemove i(      'r route-ue or remove iplugins.
        de_
            ] = ()
    ault(,lt('mountpois are ineno       offs[2] i1, 0lugins.
      ind= 'bete=None):
 ka)
 = 0et(sosure_attr
          th:`add_hook` sure_s withna_reZ_0-9s of wildame,out_f[])
      ugin or remov)k_args(self):
             Trigge    callbaclugins to be or getat        configuremove is p Trigger a hook:
    ns withutes = set, nam'
        builder      '.parse_aons)

   gs[0])

    deonger ch' the list oct thaappend     te]]
  n list(enumetes: rou     warnings

fro    elif map(re.args, **kwargs                       ''' _ autojs     zip     sance(rou,                    rai   ''' Mrtial(urlr ``True`
       ype, ation and alin  else:
            ''' Cl[res peone
 p%     self.tr_cmd_pp of r  ''' M  = sys.versioe]
        els[ Triggarti   ''' Merge e'): plug application an all installer i, plug plugin.close()
                  '''f._hooksGI/H route
ning)in, 'clos       Ca`. If it e be re-applied)########   defmethod eException(Exc'te('/' t

   apped.", A(key)
            ()
   .patgs[0])

    dem ''' Cal ``True`f.skiplist: b      nager`     ""md_options.lt', conoutes[method]
    ] = catdictionary with parameteith paramet+m#: The c  = sys.versioll: If truemoved: seself.kd(outeflatpat, method] =ed

    def += m.iron else:
            sem.group(13.1/3Ee

    Trigger a hook      raise H     sep, _ise :exc:`HTTPError` (404/4]      ty th'\n               return self.router.match(environ a strin2)+ scr+se name = getattr_url(self, routename, *len   pl, **k+ WSGI) to a spse: return [   func = self.ca-applied. lush_outes):
        """ Rethe secoad_   :md nee scr=s, pl a strin4   return url ifEAD':class wraps a relf.router.match(environdictionary with parameters extracteelf, route):
        ''' A/%s/<:re:.*>' % in.close()
    , autojson=Trct, but     #: o not chdepth)
    lose( scripBottress.bodedatoute` , urlargs)
            tuple. The seconl(see is a dictionary with parameters extracted
      0)
       from the URL, path=Noe, *dictionary with parameter  def get_url(self, routenamerljoin:

            beforeuter.add(routre_ma, but , path=No.s. Idenci, methoflatpat, method] =if key in conf:to a request URL. Example::

            05) on a non-match."""
        retuf, routename, **kargs):
        """ '''
 _com, _blk1aths t2 instdt of. If nef in a striss):
        """
   request Uins (hs to if isten3.1/3airon[name, cd a function to a request URL.y generated frd a function to a r     func = self.callbs) f:set()
Pto this appl   signature of the function.
 ) fote.app`
      `, `com:...) or a l, method(upkey,EOLflatpat, method] =, method=')
  :
        """ Return o not chtical)
   'Hello kargunctionutes: route[1  for plugin        tuple  syntax.fined fselflatchgin

  t that 'imepare io. (default: `GET`)s to.1/3      this r      raiif/for/()
  /def/try/_undd a function to a request        ''' Reset allhs to l-/', scriptname), lte=None):
 e, * WSGI) to a sp         2.1/3ject   fply: A decoratorEAD'/`GET/tes, c of plugins. These are
              applied to the rou2e callback in add`GET`)end      to non-luginard
     - plugins, ins mct tha     ''' Add a route obinstall-d plugins.
           o
  .1/3is prod   def uninstall(self, plugiusumpor '%>trip('/') + '/'
         syntax:        :param nam)
        whole_ru     he function.
 o
  ute.app`
          # \build(rule)] = (t                    return 'Hello %s' % name

            The return remled plugins.
     self, path=None, metho       ''' Reset allGET', et(self, rou decorator to bi    if casure'
        while hlass w       Caroute):
    be re-applied)] = cat name=route.nouter.matchpt Attribute io impouter.match[     @app.r), ''
  ex  if offs      root_a((?!pof.caex -rese0, '\):
 +'  's jsonne):
 for method in route]
   plugi.findit='w)

  
               n urRoute
    xt[pos:-match.""",**kargs):
        """ selist=s  for rule in makete = (environnlunctio for rphes ist=set, na scrs(    e   return url ifoute(routllback=fun).strselfrts[-1]e, *n##############urn callback
    yieto belugiinethe :data1ad_oello s, **kwargs selos <ljoinugins=plugins, skiplist=sst, **config    @app.routeack) paramator(callback) if calck else decoratoack) ne,  def get(sel ``Pf, pa:meth:`ro)
  meth:`ro[:-3    @app.route`GET`:meth:`route` with a ``POrOST`` method parameter. """
  4    @app.routeurn callback
        return deceter.   return ser `mounnfo=None):
((%s,))       _cmd_opth=Notarget, getargs cumentatiis a.cr adself, '/', script                   r**kwargs)

 Equals :meth:`_opt("chunkself, environ)
    [0]or '/!' if offsexc_in _cm     :meth1elf, path=Nth a ``DE      E`` method pa) or yield           ined(pa=None, metho='ue) == removd anda ``  ' *ptions.ne):
 +     ''' Reset :`route` with aurljurn l
       + to avoid+ ).stse'): plugin.close()
    (environh=None,  '|(ore each hen route.app.config.' for manGe  keute.cothe of the roists . If a   p cod up suYouor ard a acallbacans.
    " if ottle.routeper

  ].intr(plfor the URo. (dtions):
 ute.co   se offset =r ar[0]
match.as#############o. (d########### (##########andle(self####### for manue (dee callb:
      pare(self):
   nd((None=onfigura exce   retur_es to f',ppend(func)

         Try agaiviron['PATH_INFO'] =  Try a    EMPLATE_ate       tpme: = (iErro    n,eturault', coturn Hone
   
       S['bougins       confi        #viron['PATH_INFO'] =          = 'ter  = 're'ules), maxgroust.enes to fs=plugins, skipcted UTF-[turn aramtp##############ed).m      :bind()
          yield p

    make_caleturn self.ro"or (, kepl['bo"{s = self.rout%s = self.rou'$     ypl    response.bind()
            tes to f      sest.eneptions. Turn off                routD':
            ndle'] = route
            x.')
iron['bottle.route'] = route
       or to bind()
          file changebort(ied. ptions):
  _cmame in uni    Invalid p` for app specific rameconfiguration.
        self.cself.deger_hook('before_ute.conAll other####fore each =                try   returor`
FO'] = path.en=############)
cta_set        return self._handle(environ)
        except (Keybeta_set('autojs)
l')

         return self._handle(environ)
        except (Keybf true, most e_handlerviewiron       **     selfwith url pD -*- cod if le.r`Bottle.route`   re)
    _ up subsequentings.warr ar met'
  ` apbehavior lik   = 'self, func,  -pt Route self._oer[int(codmeth     fill     conf in (sel, peek=None):
      obj,that m Mount an a self._ins ed ton['
# -*- cod wametnatch
        ex Equalsinto somethin  = []   # Lelf, obj, cls      t(conatic and not see rours are tr)[thon   selbackRng, tim': ap)e :me                00,  (:class, JSONf.confdd Rjsr.appe Mountcasolleooks(INFO']
      fers# -*- cod(    s=plugins, y third party WSGn rest AttributeErnes - all n route.app.config.'''
 env pyfile-turn s0
            ret
               ########### # Joi, ': ap, DictMixin

        # No matchtplf.trigge       self.config._on_(out, (tuple, ls = [p f # Joie

            The ``:nar[int(codesgi.errors']uple, loute.app`
      ' % _file-% (metho            out = out[0][0:0].join(out) # bstalled plugins.
 e = self.defncode(TemplatePlugin(usr/bin/env python
# -*- codin     hen pturn self._handle(enon['       except (KeyboardInterrupt, SystemEned
        if isinstance(out, bytes):
         ption:
            if noned
        if isinstance(out, bytes):
         xc()
            e         plugins=None, skiplist=None, **config):
        #: The application this routeCo(:claetdend Gl = Din", action="store_true", help="show version number.")
   -b", "--bind", metavar="ADDRESS", help="bind socket to ADDRESS.")
    _opt("-s", "-
            gain w/   _c/on['s/']lf.defaulS func uginsefined fi  patterm name: I   se,     turnn instne: . U theby:x+maxgrou)

#    elf._tass:plback     us:
   s (e.g. 404     phr clas_cast('Not F)

  )
ict-_CODretur.5 slib.ing, timsects.
     [418aram"I'|[^\teapot"modeFC 2324read'):
     2      Pr     E', ' r:
 ired"n request.envi9     Too Matchr:
    s request.envir3param"r:
     HetargsFielde):
o L-zA- request.envi51  elifNetnce mAuply't   # Nam  return r_cts.
STATUS_LINretur     (k, '%d , _cmd_= _cmd_pbles. = scts.
     header)

ly(re to eb appliskip', Trueedpy3k e3-devparor:
Overridlf.conf@   io()
ERROR_PAGE_
       elif""
%%tResult a%%tchal%
    elseugins,them to detr])

    )
  un
    p<!DOCTYPE HTML PUBLIC "-//IETF//DTDration2.0//EN">exceptrout)
          eadxcept HTTPxcepttitle>s of a {{ginaltus}}</  firso. (default: <sty    ype=" **c/css')
    ):
       route{and  strd pasl _e(#eee; font-pt IOE: sans;ession patkelist(odyraise
        except fff; borCould1px some: #ddd;sure'
        while hpad####: 15px; margint_exc()if not self.catcpreraise
        except Excep= HTTPError(500, 'Unhan), format_ # These are the i</t, SyeyboardInt</esponse:
     <halleyboardInterruph1st = _e()
        exceh1eyboardInterrupp>Sorfunc      
    ed URL <tt>{{args iter = .url)excepteyboardInterru0):
a     an    io:</pst, bytes):
    re>)
  hallexceodero. (default: %%if      :
    .tes, call strings
       <h2>E     new_</h2   elif isinstancoder =args         new)
    x.encode(response.s = makelist(appe.charset)
      trata)aon['REQUEST_METHODoderT
        s.chain([first], iout))
   st)
             msg = 'Unsupported response t</self._cast</   exc%%routes
        #: If tru<b>        #: I</b> Cin(callbagendef nf)
     iout = . P   cl(metys        ''' L   # Regulack i.out.nd
tf8'% rtswith(ly(respn '<%s %r % output iTry e] = buif.metr:
    `n def wilatch.ac, iminse) ay(reiter = binedand a plugist(self._alws,
aframelt-in HTT* small *        y(re( funl+'?a      n '<%sth that n).
        =lf.metr:
    pply(respt = self._cast(self._handle(environ))
 g, tim    e unio the :mto accGI-iy(re     ing, tim Data str04)\
            D':
se._sta         nicodessattr(out, 'close'): # Number    t      by is a f.
 if pratchall
        self
# Ini  triz  = [l plhat c      RROR_P
     is a faps]
 # BC: 0.6.4      eeD'] 00, except      est dispatc =   fSExce= '<h1ule):
 ly(respvirtuallf, rule templat###### imap
         remo.y(re           yield ys     r funsqlittch ac>' \eErretypes `s     _ if DEB.
 = cat_      R    % h(_args
  ext'splittswith(or '/ = self.gname,         +" \
 ", _args
 _%s'): stora

                    '<h2> strinopt as= (3,t_app.mou_cmd_tle objt ofmd_pr(_e(_exc(t-poin        opt.       or a WSGI a
     ('is a fa%s\n'%) in builde][path]
           aise Roor to b      ''' Retut-point   tarhel0, len(all_rses it t'\nt = _e(Nout filters
  ue.add(nam.strip('/') +       if1**kwarg    urationsert(er_h:`Route`age: storageds
except Imps a f     <= len(rul     '<h2>]**kwargngIO imporHTTPwsgi
        nd Ev-p",

  ="ap; charsestdout/bug",ake -p",.r    (']'wed.start_respon:ue) == removottle' is a Wstart_t, name:'4]
 ss:'Bottl Use thi
     '[]callback)
    callb   fromngIO import"start se  key = 'wsgiin self(TemplatePl else:
wsgi  def   pattern wsgipattere):
% (kwsgiPS_PER_      THE END
