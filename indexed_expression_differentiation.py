from sympy import *
from sympy.printing.str import StrPrinter
from sympy.printing.latex import LatexPrinter
from itertools import groupby
from collections import Counter
import re
import pprint

K,J,T = symbols('K J T', integer=True)
k,j,t = symbols('k j t', integer=True)

# python evaluates 1/2 to 0, so use 0.5 or S(1)/2
# free_energy = -(S(1)/2)*Sum(Sum(log(2*pi*sigma[k,t]),(k,1,K)),(t,1,T)) -K*T/2+ Sum(Sum(m[k,t]*log(m[k,t]),(k,1,K)),(t,1,T))+S(1)/2*K*T*log(2*pi*alpha**2) + Sum(Sum((mu[k,t]**2 + sigma[k,t])/(2*alpha**2),(k,1,K)),(t,1,T)) + T*log(K)-J*T/2*log(beta/(2*pi))+beta/2*Sum(Sum(y[j,t]**2-2*y[j,t]*Sum(w[j,k]*mu[k,t]*m[k,t],(k,1,K))+Sum(w[j,k]**2*(mu[k,t]**2+sigma[k,t])*m[k,t],(k,1,K)),(t,1,T)),(j,1,J))

indices = set([k,j,t])

Summ = Function("Summ",commutative=True)

IDX_DIFF_RULES = { 
         
        # e =expression, s = a list of symbols respsect to which
        # we want to differentiate
         
        Symbol : lambda e,s : 0,
        Sum : lambda e,s : idxDiff(reduce(lambda x,I: x.subs(I[0],I[1]) if I[0] in indices else Sum(x,(I[1],1,I[0])), [(idxs[0],idxs[2]) if idxs[2] in get_indices(s)[0] else (idxs[2],idxs[0]) for idxs in e.args[1:]], e.args[0]),s),
        Add :  lambda e,s : Add(*[idxDiff(arg,s) for arg in e.args]),
        Mul :  lambda e,s : Mul(idxDiff(e.args[0],s),Mul(*e.args[1:]))
                      +  Mul(e.args[0],idxDiff(Mul(*e.args[1:]),s)) ,
        log : lambda e,s : S(1)/e.args[0] if e==log(s) else Mul(idxDiff(e.args[0],s),S(1)/e.args[0]),
        Summ : lambda e,s : Summ(idxDiff(e.args[0],s),e.args[1]),
        Pow : lambda e,s : Mul(idxDiff(e.args[0],s),e.args[1]*Pow(e.args[0],e.args[1]-1)),
        exp : lambda e,s : Mul(idxDiff(e.args[0],s),exp(e.args[0])),
}

def idxDiff(expr,symbol,verbose=0):
    #pdb.set_trace()
    if symbol.free_symbols.intersection(expr.free_symbols) != symbol.free_symbols:
        return 0
    if expr == symbol:
        return 1
    if expr.__class__ in IDX_DIFF_RULES.keys():
        if verbose:
            print expr, expr.__class__
        if expr.__class__ == Sum: # always expand sums
            if all([idx[-1] not in get_indices(symbol)[0] for idx in expr.args[1:]]):
                expr = Summ(expr.args[0],*expr.args[1:])
            expr = expr.expand()

        return  IDX_DIFF_RULES[expr.__class__](expr,symbol)
    else:
        return 0
###

def expr2tree(expr):
    if expr.func in [Indexed, Symbol, Integer]:
        return [(expr.func, expr)]
    else:
        return [(expr.func, expr.args), [expr2tree(arg) for arg in expr.args]]

def tree2expr(tree):
    #pdb.set_trace()
    if tree[0][0] in [Symbol,Integer,Indexed]:
        return tree[0][1]
    elif all([arg.args == () for arg in tree[0][1]]):
        return tree[0][0](*tree[0][1])
    else:
        return tree[0][0](*[tree2expr(i) for i in tree[1]])

def factors_inside_sums(tree):
    if tree[0][0] in [Symbol,Integer,Indexed]:
        return tree[0][1]
    elif all([arg.args == () for arg in tree[0][1]]):
        return tree[0][0](*tree[0][1])
    else:
        if tree[0][0] == Mul and Sum in [factor[0][0] for factor in tree[1] if hasattr(factor[0],'__iter__')]:
            the_sum = [tree2expr(factor) for factor in tree[1] if factor[0][0] == Sum]
            inside_sum = [tree2expr(factor) for factor in tree[1] if factor[0][0] != Indexed and factor[0][0] != Sum]
            outside_sum = [tree2expr(factor) for factor in tree[1] if factor[0][0] == Indexed]
            #pdb.set_trace()
            return Mul(Sum(Mul(the_sum[0].args[0],*inside_sum),*the_sum[0].args[1:]),*outside_sum)
        else:
            return tree[0][0](*[factors_inside_sums(i) for i in tree[1]])

def factors_outside_sums(tree):
    if tree[0][0] in [Symbol,Integer,Indexed]:
        return tree[0][1]
    elif all([arg.args == () for arg in tree[0][1]]):
        return tree[0][0](*tree[0][1])
    else:
        if tree[0][0] == Sum and tree[1][0][0][0] == Mul: 
            #pdb.set_trace()
            expr = tree2expr(tree)
            idxs = [idx[0] for idx in expr.args[1:]]
            idxs_in_sum = []
            for arg in expr.args[0].args:
                try:
                    idxs_in_sum.append(get_indices(arg)[0])
                except:
                    idxs_in_sum.append(set(idxs))
            factors_inside = [expr.args[0].args[i] for (i,idx_in_sum) in enumerate(idxs_in_sum) if set(idxs).intersection(idx_in_sum)]
            factors_outside = [i for i in expr.args[0].args if i not in factors_inside]
            return Mul(Sum(Mul(*factors_inside),*expr.args[1:]),*factors_outside)
        else:
            return tree[0][0](*[factors_outside_sums(i) for i in tree[1]])


def gather_sums(tree):
    if tree[0][0] in [Symbol,Integer,Indexed]:
        return tree[0][1]
    elif all([arg.args == () for arg in tree[0][1]]):
        return tree[0][0](*tree[0][1])
    else:
        if tree[0][0] == Add and any([c>1 for c in Counter([idx for term in [term[0][1][1:] for term in tree[1] if term[0][0] == Sum] for idx in term]).values()]):
            sumidx = [i for (i,term) in enumerate(tree[1]) if term[0][0] == Sum]
            restidx = [i for i in range(len(tree[1])) if i not in sumidx]
            #pdb.set_trace()
            return Add(Sum(Add(*[tree2expr(i) for i in [tree[1][j][1][0] for j in sumidx]]),*[tree2expr(i) for i in tree[1][sumidx[0]][1][1:]]),*[tree2expr(i) for i in [tree[1][j] for j in restidx]])
        if tree[0][0] == Mul and any([c>1 for c in Counter([idx for term in [term[0][1][1:] for term in tree[1] if term[0][0] == Sum] for idx in term]).values()]):
            return Sum(Mul(*[tree2expr(factor[1][0]) for factor in tree[1]]),*max([term[0][1][1:] for term in tree[1] if term[0][0] == Sum],key=len))
        else:
            return tree[0][0](*[gather_sums(i) for i in tree[1]])

def gradient(expr,symbols):
    grad = []
    for symbol in symbols:
        grad.append(factors_outside_sums(expr2tree(gather_sums(expr2tree(factors_inside_sums(expr2tree(idxDiff(expr,symbol).replace(Summ,Sum).simplify())).simplify())).simplify())))
        #grad.append(factors_outside_sums(expr2tree(factors_inside_sums(expr2tree(gather_sums(expr2tree(factors_inside_sums(expr2tree(idxDiff(expr,symbol).replace(Summ,Sum))))))))).simplify())
    return grad

def update_eqs(expr,symbols):
    updateeqs = []
    if type(expr) != list:
        grad = gradient(expr, symbols)
    else:
        grad = expr

    for (partial_derivative,symbol) in zip(grad,symbols):
        updateeqs.append(solve(partial_derivative.simplify(),symbol)[0])
    return updateeqs

def mylatex(x):
    tmp = latex(x)
    for snask in re.split(r'\s[a-z]\s',' q '.join(re.findall(r'\\substack\{.*?\}',tmp))):
        tmp = tmp.replace(snask, "")
    return re.sub(' q ', '',re.sub(r', ', r'\n', tmp))


gamma = Symbol('gamma')
x = IndexedBase('x')
m = IndexedBase('m')
w = IndexedBase('w')
mu = IndexedBase('mu')
sigma = IndexedBase('sigma')
y = IndexedBase('y')
beta = Symbol('beta')
alpha = Symbol('alpha')

negF1 = S(1)/2*J*T*log(beta/(2*pi)) - beta/2*Sum((y[j,t] - Sum(w[j,k]*m[k,t]*x[k,t],(k,1,K)))**2,(t,1,T),(j,1,J)) - beta/2*Sum(w[j,k]**2*x[k,t]**2*(m[k,t]-m[k,t]**2),(k,1,K),(t,1,T),(j,1,J))
negF2 = gamma*Sum(m[k,t],(t,1,T),(k,1,K))-K*T*log(1+exp(gamma))
negF3 = -Sum(m[k,t]*log(m[k,t])+(1-m[k,t])*log(1-m[k,t]),(t,1,T),(k,1,K))
neg_free_energy = negF1+negF2+negF3

print factors_inside_sums(expr2tree(idxDiff(free_energy2,m[K,T]).replace(Summ,Sum).simplify()))

print mylatex(gradient(neg_free_energy,[w[J,K],m[K,T],x[K,T],beta,gamma]))
grad = gradient(neg_free_energy,[w[J,K],m[K,T],x[K,T],beta,gamma])

solve(grad[-1],gamma)

pp = pprint.PrettyPrinter(indent=4)
wtree = expr2tree(grad[0])
pp.pprint(wtree)