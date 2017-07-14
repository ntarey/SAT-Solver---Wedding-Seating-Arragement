clauses = []
propSymbols = set()
model = {}

class Clause:
    literals = []

    def __init__(self, literals):
        self.literals = literals
        self.positives = []
        self.negatives = []

    def setPositives(self, l):
        self.positives = l

    def setNegatives(self, l):
        self.negatives = l

    def getPositives(self):
        return self.positives

    def getNegatives(self):
        return self.negatives


class Literal:
    def __init__(self, name, guest, table, sign):
        self.name = name
        self.guest = guest
        self.table = table
        self.sign = sign

def get_cnf():
    global clauses
    for i in range(1,num_guests+1):
        item = []
        p =[]
        for j in range(1,num_tables+1):
            name = "X_" + str(i) + "_" + str(j)
            l = Literal(name, str(i),str(j),'')
            p.append(name)
            propSymbols.add(name)
            item.append(l)
        c = Clause(item)
        c.setPositives(p)
        clauses.append(c)


    for i in range(1,num_guests+1):
        for j in range(1,num_tables+1):
            for k in range(j,num_tables+1):
                item =[]
                n = []
                if j != k:
                    namel = "X_" + str(i) + "_" + str(j)
                    namem = "X_" + str(i) + "_" + str(k)
                    l = Literal(namel, str(i),str(j),'~')
                    m = Literal(namem, str(i),str(k),'~')
                    item.append(l)
                    item.append(m)
                    propSymbols.add(namel)
                    propSymbols.add(namem)
                    c = Clause(item)
                    n.append(namel)
                    n.append(namem)
                    c.setNegatives(n)
                    clauses.append(c)


    for i in range(0,len(friends)):
        for j in range(1,num_tables+1):
            item = []
            p = []
            n = []
            a = friends[i][1]
            b = friends[i][2]
            namel = "X_" + a + "_" + str(j)
            namem = "X_" + b + "_" + str(j)
            l = Literal(namel, a,str(j),'~')
            m = Literal(namem, b,str(j), '')
            p.append(namem)
            n.append(namel)
            item.append(l)
            item.append(m)
            propSymbols.add(namel)
            propSymbols.add(namem)
            c = Clause(item)
            c.setNegatives(n)
            c.setPositives(p)
            clauses.append(c)
            item = []
            p = []
            n = []
            namel = "X_" + a + "_" + str(j)
            namem = "X_" + b + "_" + str(j)
            l = Literal(namel,a,str(j),'')
            m = Literal(namem,b,str(j),'~')
            p.append(namel)
            n.append(namem)
            item.append(l)
            item.append(m)
            propSymbols.add(namel)
            propSymbols.add(namem)
            c1 = Clause(item)
            c1.setNegatives(n)
            c1.setPositives(p)
            clauses.append(c1)

    for i in range(0,len(enemies)):
        for j in range(1,num_tables+1):
            item = []
            n = []
            a = enemies[i][1]
            b = enemies[i][2]
            namel = "X_" + a + "_" + str(j)
            namem = "X_" + b + "_" + str(j)
            l = Literal(namel,a,str(j),'~')
            m = Literal(namem,b,str(j),'~')
            n.append(namel)
            n.append(namem)
            item.append(l)
            item.append(m)
            propSymbols.add(namel)
            propSymbols.add(namem)
            c3 = Clause(item)
            c3.setNegatives(n)
            clauses.append(c3)

def intersection(a,b):
    result = []
    for x in a:
        for y in b:
            if x == y:
                result.append(x)
    return result

def dpll_satisfiable():
    global clauses, propSymbols
    return dpll(clauses,propSymbols,model)

def dpll(clauses,propSymbols,model):

    if everyClauseTrue(clauses,model):
        return True
    if someClauseFalse(clauses, model):
        return False

    p,value = findPureSymbol(propSymbols,clauses, model)
    if p != None:
        if p in propSymbols:
            propSymbols.remove(p)
        return dpll(clauses,propSymbols,updateModel(model,p,value))
    p,value = findUnitClause(clauses,model)
    if p != None:
        if p in propSymbols:
            propSymbols.remove(p)
        return dpll(clauses,propSymbols,updateModel(model,p,value))

    if not propSymbols:
        return True

    symbolList = list(propSymbols)
    p = symbolList[0]
    rest = symbolList[1:]

    return dpll(clauses, rest, updateModel(model,p,True)) or dpll(clauses, rest, updateModel(model,p,False))

def updateModel(model, p, value):
    model.update({p:value})
    return model

def findUnitClause(clauses,model):
    result = None, None
    for c in clauses:
        if determineValue(c) == None:
            unassigned = None

            if len(c.literals) == 1:
                unassigned = c.literals[0]
            else:
                for l in c.literals:
                    value = model.get(l.name)
                    if value == None:
                        if unassigned == None:
                            unassigned = l
                        else:
                            unassigned = None
                            break
            if unassigned != None:
                if unassigned.sign == '~':
                    sign = False
                else:
                    sign = True
                result = unassigned.name,sign
                break
    return result

def findPureSymbol(propSymbols,clauses, model):
    result = None, None
    candidatePos = set()
    candidateNeg = set()

    for c in clauses:

        if determineValue(c) == True:
            continue

        for p in c.getPositives():
            if p in propSymbols:
                candidatePos.add(p)


        for n in c.getNegatives():
            if n in propSymbols:
                candidateNeg.add(n)

    for s in propSymbols:

        if s in candidatePos and s in candidateNeg:
            candidatePos.remove(s)
            candidateNeg.remove(s)

    if len(candidatePos) > 0:
        p = candidatePos.pop()
        result = p, True

    elif len(candidateNeg) > 0:
        n = candidateNeg.pop()
        result = n, False

    return result

def everyClauseTrue(clauses, model):
    return satisfies(clauses)

def satisfies(clauses):
    for c in clauses:
        if not determineValue(c) == True:
            return False
    return True


def someClauseFalse(clauses, model):
    for c in clauses:
        val = determineValue(c)
        if val == False:
            return True
    return False


def determineValue(c):
    result = None

    if isTautology(c):
        result = True
    elif isFalse(c):
        result = True
    else:
        unassignedSymbols = False
        value = None
        for pos in c.positives:
            value = model.get(pos)
            if value != None :
                if value == True:
                    result = True
                    break
            else:
                unassignedSymbols = True

        if result == None:
            for neg in c.negatives:
                value = model.get(neg)
                if value != None :
                    if value == False:
                        result = True
                        break
                else:
                    unassignedSymbols = True

            if result == None:
                if not unassignedSymbols:
                    result = False

    return result

def isTautology(c):
    positives = c.getPositives()
    negatives = c.getNegatives()
    intersect = intersection(positives,negatives)
    if(len(intersect) > 0):
        return True
    else:
        return False


def isFalse(c):
    return len(c.literals) == 0

def main():
    file = open("input.txt", 'r')
    lines = file.read().splitlines()
    global num_guests, num_tables, friends, enemies, clauses
    line = lines[0].split(" ")
    num_guests = int(line[0])
    num_tables = int(line[1])
    friends = []
    enemies = []
    for i in range(1,len(lines)):
        if lines[i][4] == 'F':
            item = []
            item.append(lines[i][4])
            item.append(lines[i][0])
            item.append(lines[i][2])
            friends.append(item)
        else:
            item = []
            item.append(lines[i][4])
            item.append(lines[i][0])
            item.append(lines[i][2])
            enemies.append(item)

    if num_guests <= 0 or num_tables <= 0:
        result = False

    else:
        get_cnf()
        result = dpll_satisfiable()

    op_file = open("output.txt", 'a')

    if result == False:
        print >> op_file, "no"

    if result == True:
        print >> op_file, "yes"
        assignments = {}
        for k in model.iterkeys():
            if model.get(k) == True:
               key = k.split('_')
               assignments.update({key[1]:key[2]})

        for g in sorted(assignments.iterkeys(), key=lambda key_value: int(key_value[0:])):
            print >> op_file, g + " " + assignments.get(g)

    file.close()
    op_file.close()

main()
