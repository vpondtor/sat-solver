import sys
from copy import copy, deepcopy
import random
import unittest
import glob
 
# Feel free to change the provided types and parsing code to match
# your preferred representation of formulas, clauses, and literals.
 
class Literal:
    def __init__(self, name, sign):
        self.name = name  # integer
        self.sign = sign  # boolean
 
    def __repr__(self):
        return ("-" if not self.sign else "") + self.name
 
    def __eq__(self, other):
        if type(other) != Literal:
            return False
        return self.name == other.name and self.sign == other.sign
 
    def __hash__(self):
      return hash((self.name, self.sign))
 
    def negate(self):
        return Literal(self.name, not self.sign)
 
 
class Clause:
    def __init__(self, id, literalSet):
        self.id = id
        self.literalSet = literalSet
 
    def __repr__(self):
        return f"{self.id}: {str(self.literalSet)}"
 
    def __eq__(self, other):
        if type(other) != Clause:
            return False
        return self.id == other.id
 
 
 
 
#Given a set of clauses and literals and partial assignment, returns a simplified clause
#Where all variables are assigned based on the partial assignment
def reduction(Clauses, Literals, partialAssignment, assignmentMod):
    for i in range(len(assignmentMod)):
        # Literal is modified
        if (assignmentMod[i] != 1): 
            lit = Literals[i]
            partialAssignment[i] = partialAssignment[i] * assignmentMod[i]
            trueLit = lit if partialAssignment[i] == 1 else lit.negate()
            falseLit = trueLit.negate()
            # remove clauses with true occurences of the literal
            Clauses = list(filter(lambda c: trueLit not in c.literalSet, Clauses))
            # remove false occurences of literals from litsets
            Clauses = list(map(lambda c: Clause(c.id, list(filter(lambda l: l != falseLit, c.literalSet))), Clauses))

    return Clauses, partialAssignment
 
 
#Returns the modified clauses and assignment after performing unit clause elimination
def unitClauseEliminate(Clauses, Literals, assignment):
 
    unitClauses = list(filter(lambda clause: len(clause.literalSet) == 1, Clauses))
 
    while(len(unitClauses) != 0):
        assignmentMod = [1 for x in range(len(Literals))]
 
        for unitClause in unitClauses:
            lit = unitClause.literalSet[0]
 
            #Set assignment modification vector
            assignmentMod[Literals.index(Literal(lit.name,True))] = -1 if lit.sign else 0
 
        #Perform reduction on currrent unit Clauses
        Clauses, assignment = reduction(Clauses,Literals,assignment,assignmentMod)
 
        #Revaluate existence of unit clauses
        unitClauses = list(filter(lambda clause: len(clause.literalSet) == 1, Clauses))
 
    return Clauses, assignment
                
def isPure(literal, formula):
    exists = False
    for clause in formula:
        if (literal.negate() in clause.literalSet):
            return False
        elif (literal in clause.literalSet):
            exists = True
    return exists
 
 
#Returns clauses and assignment after performing pure literal elimination
def pureLiteralEliminate(Clauses, Literals, assignment):
    
    assignmentMod = [1 for x in range(len(Literals))]
 
    for literal in Literals:
        if isPure(literal, Clauses):
            # Set the assignment
            assignmentMod[Literals.index(literal)] = -1
 
        if isPure(literal.negate(), Clauses):
            # Set the assignment
            assignmentMod[Literals.index(literal)] = 0
 
    Clauses, assignment = reduction(Clauses, Literals, assignment, assignmentMod)
 
    return Clauses, assignment
 
 
#Given a set of clauses and literals returns a bitvector of assignments
def solve(Clauses, Literals, assignment):
    
    Clauses, assignment = pureLiteralEliminate(Clauses, Literals, assignment)
   
    Clauses, assignment = unitClauseEliminate(Clauses, Literals, assignment)
 
    #check for empty clauses
    if any(map(lambda c: len(c.literalSet) == 0,Clauses)):
        return None
 
    #pick first unassigned var, branch
    try:
        branchVar = assignment.index(-1)
        assignmod = [1 for x in range(len(Literals))]
        # Try with branchVar True
        assignmod[branchVar] = -1
        bClauses, bAssignment = reduction(Clauses, Literals, assignment, assignmod)
        result = solve(bClauses, Literals, bAssignment)
        if result is not None:
            return result
 
        # Try with branchVar False
        assignmod[branchVar] = 0
        bClauses, bAssignment = reduction(Clauses, Literals, assignment, assignmod)
        return solve(bClauses, Literals, bAssignment)
 
    except ValueError:
        #No occurences of unassigned variables
        #We are done
        assert len(Clauses) == 0
        return assignment
 
# Read and parse a cnf file, returning the variable set and clause set
def readInput(cnfFile):
    variableSet = []
    clauseSet = []
    nextCID = 0
    with open(cnfFile, "r") as f:
        for line in f.readlines():
            tokens = line.strip().split()
            if tokens and tokens[0] != "p" and tokens[0] != "c":
                literalSet = []
                for lit in tokens[:-1]:
                    sign = lit[0] != "-"
                    variable = lit.strip("-")
 
                    literalSet.append(Literal(variable, sign))
                    if variable not in variableSet:
                        variableSet.append(variable)
 
                clauseSet.append(Clause(nextCID, literalSet))
                nextCID += 1
    
    return variableSet, clauseSet
 
# Print the result in DIMACS format
def printOutput(assignment,Literals):
    result = ""
    isSat = (assignment is not None)
    if isSat:
        for i in range(len(assignment)):
            result += " " + ("" if assignment[i] else "-") + str(Literals[i])
 
    print(f"s {'SATISFIABLE' if isSat else 'UNSATISFIABLE'}")
    if isSat:
        print(f"v{result} 0")


# Determines if an assignment will produce a valid solution
def validSolution(Clauses, Literals, assignment):
    for clause in Clauses:
        if not trueClause(clause, Literals, assignment):
            return False
    return True


def trueClause(clause, Literals, assignment):
    for lit in clause.literalSet:
        signless = Literal(lit.name, True)
        if lit.sign:
            if assignment[Literals.index(signless)]:
                return True
        else:
            if not assignment[Literals.index(signless)]:
                return True
    return False
 

class TestFunctions(unittest.TestCase):
    # Clauses, Literals, partialAssignment, assignmentMod
    # Clauses, Literals, assignment
    def testUnitClauseEliminate(self):

        # No clauses
        testClauses = []
        testLiterals = []
        testAssignment = []
        newClauses, newAssignment = unitClauseEliminate(testClauses, testLiterals, testAssignment)
        self.assertEqual(newClauses, [])
        self.assertEqual(newAssignment, [])

        # One unit clause
        testClauses = [Clause(0, [Literal(1, True)])]
        testLiterals = [Literal(1, True)]
        testAssignment = [-1]
        newClauses, newAssignment = unitClauseEliminate(testClauses, testLiterals, testAssignment)
        self.assertEqual(newClauses, [])
        self.assertEqual(newAssignment, [1])

        # One negative unit clause
        # testClauses = [Clause(0, [Literal(1, True)])]
        # testLiterals = [Literal(1, True)]
        # testAssignment = [-1]
        # newClauses, newAssignment = unitClauseEliminate(testClauses, testLiterals, testAssignment)
        # self.assertEqual(newClauses, [])
        # self.assertEqual(newAssignment, [0])

        # Two clauses, both unit clauses
        testClauses = [Clause(0, [Literal(1, True)]), Clause(1, [Literal(2, True)])]
        testLiterals = [Literal(1, True), Literal(2, True)]
        testAssignment = [-1, -1]
        newClauses, newAssignment = unitClauseEliminate(testClauses, testLiterals, testAssignment)
        self.assertEqual(newClauses, [])
        self.assertEqual(newAssignment, [1, 1])

    


    # def testReduction(self):
    #     c = []
    #     l = []
    #     partialAssignment = []
    #     modifications = []
    #     self.assertEqual(unitClauseEliminate(c, l, partialAssignment, modifications), (resultClause, resultAssignment))
    
    def test_solve(self):
        # List of (fileName, answer) tuples
        testSuite = [
            ("tests/all_neg.cnf", [0, 0, 0, 0, 0, 0, 0]),
            ("tests/all_pos.cnf", [1, 1, 1, 1, 1]),
            ("tests/empty_clause.cnf", None),
            ("tests/empty_clause.cnf", None),
            # The empty test is a weird one
            ("tests/empty.cnf", []),
            ("tests/generic.cnf", [1, 1, 1, 1, 0]),
            ("tests/invalid.cnf", None),
            ("tests/multiple_clause_unsat.cnf", None),
            ("tests/neg_one_literal.cnf", [0]),
            ("tests/one_clause.cnf", [1, 1, 0, 1, 0, 0, 0, 1, 1, 1]),
            ("tests/one_literal.cnf", [1]),
            ("tests/one_solution.cnf", [1, 0, 1, 0, 1]),
            ("tests/test.cnf", [1, 1, 1]),
            ("tests/two_clause_unsat.cnf", None),
        ]

        for item in testSuite:
            varbset, clauseSet = readInput(item[0])
            Literals = list(map(lambda v: Literal(v,True), varbset))
            result = solve(clauseSet,Literals,[-1 for x in range(len(varbset))])
            self.assertEqual(result, item[1])
            # if (result != None):
            #     myBool = validSolution(clauseSet, Literals, result)
            #     self.assertTrue(validSolution(clauseSet, Literals, result))


    def test_validation_only(self):
        # Finds all files in test directory that end w/ .cnf
        testSuite = [f for f in glob.glob("./tests/*.cnf")]
        for path in testSuite:
                varbset, clauseSet = readInput(str(path))
                Literals = list(map(lambda v: Literal(v,True), varbset))
                result = solve(clauseSet,Literals,[-1 for x in range(len(varbset))])
                if (result != None):
                    # If there is a solution, ensure that it is a valid solution
                    self.assertTrue(validSolution(clauseSet, Literals, result))

            
        
if __name__ == "__main__":
    # unittest.main()
    inputFile = sys.argv[1]
    varbset, clauseSet = readInput(inputFile)
 
    # TODO: find a satisfying instance (or return unsat) and print it out
    Literals = list(map(lambda v: Literal(v,True), varbset))
    printOutput(solve(clauseSet,Literals,[-1 for x in range(len(varbset))]), Literals)
