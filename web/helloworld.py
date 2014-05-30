#coding:utf8
from bottle import route, run, template

@route('/hello/<name>')
def index(name):
    return template('<b>Hello {{name}}</b>!', name=name)


@route('/')
def home():
    return template('welcome.html')
    
    
run(host='localhost', port=8080)