verbose = True
NoGood = '⊥'
PHI = set([frozenset()])
leftSpace = 11
#frozensets are environments

rules = list()
# list of tuples of assumptions as set() and propositions as char
# just use horn clauses to define rules!

rules_ex1 = list()
rules_ex1.append( ({'A'}, 'a') )
rules_ex1.append( ({'B','b'}, 'e') )
rules_ex1.append( ({'C','a'}, 'f') )
rules_ex1.append( ({'C','e'}, 'g') )
rules_ex1.append( ({'D'}, 'e') )
rules_ex1.append( ({'E'}, 'e') )
rules_ex1.append( ({'a','e'}, NoGood) )
rules_ex1.append( ({'g','f'}, NoGood) )
rules_ex1.append( ({'E'}, 'b') )

# Nixon Diamond Problem, https://en.wikipedia.org/wiki/Nixon_diamond
rules_nixon = list()
rules_nixon.append( ({'q','Dq'}, 'p') )
rules_nixon.append( ({'r','Dr'}, 'np') )
rules_nixon.append( (set(), 'q') )
rules_nixon.append( (set(), 'r') )
rules_nixon.append( ({'p','np'}, NoGood) )

rules_coffee = list()
rules_coffee.append( ({'Request'}, 'request') )
rules_coffee.append( ({'Water'}, 'water') )
rules_coffee.append( ({'Beans'}, 'beans') )
rules_coffee.append( ({'request','water','beans'}, 'coffee') )
rules_coffee.append( ({'coffee'}, 'request') )
rules_coffee.append( ({'coffee'}, 'water') )
rules_coffee.append( ({'coffee'}, 'beans') )
rules_coffee.append( ({'no_coffee','request','water'}, 'no_beans') )
rules_coffee.append( ({'no_coffee','request','beans'}, 'no_water') )
rules_coffee.append( ({'no_coffee','water','beans'}, 'no_request') )
rules_coffee.append( ({'beans','no_beans'}, NoGood) )
rules_coffee.append( ({'request','no_request'}, NoGood) )
rules_coffee.append( ({'water','no_water'}, NoGood) )
rules_coffee.append( ({'coffee','no_coffee'}, NoGood) )

rules = rules_ex1 #rules_coffee

nodes = dict() # dict with char as keys and sets as value



def isEmpty(S):
    return (len(S) == 0)

def ANTECEDENCE(rule):
    return rule[0]

def CONSEQUENT(rule):
    return rule[1]

def PROPAGATE(rule, a, I):
    if verbose: print("PROPAGATE:".ljust(leftSpace), rule, a, I)
    L = WEAVE(a, I, ANTECEDENCE(rule))
    if isEmpty(L):
        return
    UPDATE(L, CONSEQUENT(rule))

def WEAVE(p, I, X:set):
    if verbose: print("WEAVE:".ljust(leftSpace), p, I, X)
    # 1. Terminiation Condition
    if isEmpty(X):
        return I

    # 2. Iterate over the antecedence nodes
    R = X.copy()    # tail of X
    h = R.pop()     # head of X

    # 3. Avoid computing the full label
    if h is p:
        return WEAVE(PHI, I, R)

    # 4. Incrementally construct the label
    I_new = set()
    for env in I:
        h_val =  nodes.get(h)
        if (h_val == None or h_val == set()):
            nodes[h] = set()
            new = set(h).union(env)
            I_new.add(frozenset(new))
        else:
            dummy = 1
            for env_h in nodes[h]:
                new = set()
                new.update(*env_h)
                new.update(env)
                I_new.add(frozenset(new))
            dummy = 2

    # 5. Ensure Minimality and no inconsistenty
    # no duplicate env possibel, because of python set
    minimizeLabel(I_new, True)

    # 6. Rekursion
    return WEAVE(p, I_new, R)

def minimizeLabel( label:set, andNoGoods=False ):
    removeEnvs = set()

    if andNoGoods:
        for env in label:
            if NoGood in env:
                removeEnvs.add(env)

    for env_i in label:
        for env_j in label:
            if env_i == env_j: continue
            if env_i.issuperset(env_j):
                removeEnvs.add(env_i)

    for rEnv in removeEnvs:
        label.remove(rEnv)

def UPDATE(L, n):
    if verbose: print("UPDATE:".ljust(leftSpace), *L, n)
    # 1. Detect NOGOOD
    if n == NoGood:
        for E in L:
            NOGOOD(E)
        return

    # 2. Update and ensure minimality
    nodeVal = nodes.get(n)
    if nodeVal == None:
        nodes[n] = set(L)
    else:
        #2a:
        removeEnvs = set()
        for env_l in L:
            for env_n in nodes[n]:
                if env_l.issuperset(env_n):
                    removeEnvs.add(env_l)
        for r in removeEnvs:
            L.remove(r)
        #2b:
        removeEnvs = set()
        for env_l in L:
            for env_n in nodes[n]:
                if env_n.issuperset(env_l):
                    removeEnvs.add(env_n)
        for r in removeEnvs:
            nodes[n].remove(r)
        #2c:
        nodeVal = nodes.get(n)
        nodes[n] = nodeVal.union(L)
        if verbose: print("LABEL:".ljust(leftSpace), *nodes[n], " for ", n)

    # 3. Propagate to consequences
    for J in rules:
        if n in ANTECEDENCE(J):

            # 3b Remove Subsumed and inconsistant
            if nodes.get(CONSEQUENT(J)) is not None:
                removeEnvs = set()
                for env in nodes.get(CONSEQUENT(J)):
                    if env.issuperset(n):
                        removeEnvs.add(env)
                for r in removeEnvs:
                    nodes.get(CONSEQUENT(J)).remove(r)

            # 3a Propagate
            PROPAGATE(J, n, L)


def NOGOOD(E):
    if verbose: print("NOGOOD:".ljust(leftSpace), E)
    if nodes.get(NoGood) == None:
        nodes[NoGood] = set()

    # 2. Remove E from any superset in every node lable
    # TODO: I'm not sure if this is okay!?
    for n in nodes:
        removeSet = set()
        for env in nodes[n]:
            if env.issuperset(E):
                if verbose: print("REMOVED:".ljust(leftSpace), E, " from ", n, ": ", nodes[n])
                removeSet.add(env)
        for remEnv in removeSet:
            nodes[n].remove(remEnv)

    # 1. Mark E as nogood
    nodes[NoGood].add(frozenset(E))

    minimizeLabel(nodes[NoGood])

def getEnvString(setOfEnvs):
    string = ""
    for env in setOfEnvs:
        string += '{'
        for elem in env:
            string += str(elem)
            string += ", "
        string = string[:-2]
        string += '} '
    return string

def processRules():
    maxRuleLen = 0
    for r in rules: maxRuleLen = max(maxRuleLen, len(str(r[0])))
    for r in rules: print(str(r[0]).ljust(maxRuleLen), ' -> ', r[1])

    for rule in rules:
        print()

        PROPAGATE(rule, PHI, set([frozenset()]))

        print()
        maxNodeName = 0
        for k in nodes.keys() : maxNodeName = max(maxNodeName, len(k))
        for n in sorted(nodes):
            if str(n).isupper(): continue   # comment to show assumptions
            print(str(n).ljust(maxNodeName), end=" : ")
            if nodes[n] == set():
                print('')
            else:
                print(getEnvString(nodes[n]))


processRules()