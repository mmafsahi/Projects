# KenKen puzzle solver
# reference from: https://github.com/chanioxaris/kenken-solver
import sys, re, time, random, csp, operator

class Cage():
	"""
	Denote a Cage in the puzzle.
	"""
	def __init__(self, name):
		self.goal = -1
		self.opr  = ''
		self.id   = name
		self.vars = list()

	def __repr__(self):
		return "<id: " + self.id + ", goal: " + str(self.goal) + self.opr + ", vars: " + str(self.vars) + ">"

	def __eq__(self, other):
		if isinstance(other, Cage) and self.id == other.id:
			return True
		return False


class Kenken():
	"""
	Class to denote a Kenken puzzle and methods to solve it
	"""
	def __init__(self, filename):
		# parse data file and populate all data structures
		with open(filename, 'r') as file:
			# N          - kenken board size
			# variables  - [0, 1, ..., N*N-1] one for each board location
			# domains    - {var: [val0, val1, .., valk]} map of all possible values for each variable
			# neighbors  - {var: [var0, var1, .., vark]} map of all same row or col variables for each variable
			#
			# cage_board - cage_board[i][j] = cage id for (i, j)
			# cage_dict  - {cage_id: Cage} map of Cage objects for all cages. 
			self.N          = int(file.readline().strip())
			self.variables  = list(i for i in range(self.N*self.N))
			self.domains    = dict((v, list(i for i in range(1, self.N+1)) )for v in self.variables)
			self.neighbors  = dict()

			self.cage_board = list(list(0 for i in range(self.N)) for j in range(self.N))
			self.cage_dict  = dict()

			for i in range(self.N):
				# now read next N lines to find which
				# cell belongs to which cage (see input data file)
				line = file.readline().strip()
				for j in range(len(line)):
					cage_id = line[j]          # making it case insensitive: may help for larger puzzles
					self.cage_board[i][j] = cage_id

					if not cage_id in self.cage_dict:
						self.cage_dict[cage_id] = Cage(cage_id)
					self.cage_dict[cage_id].vars.append(self.xy_to_variable(i, j))

			# next, read goals for each cage
			for i in range(len(self.cage_dict)):
				line    = file.readline().strip()        # e.g 'A:240*'
				toks    = line.split(":")                #     ['A', '240*']
				cage_id = toks[0].strip()

				opr     = re.sub('[0-9]', '', toks[1])   # replace digits in 240* with ''
				goal    = int(toks[1].replace(opr, ''))

				self.cage_dict[cage_id].opr  = opr
				self.cage_dict[cage_id].goal = goal

				if opr == '-' or opr == '/':
					# ensure subtract or divide cage have only 2 locations
					assert len(self.cage_dict[cage_id].vars) == 2
				elif opr == '=':
					# ensure identity cage has only 1 location
					assert len(self.cage_dict[cage_id].vars) == 1

			# populate the dict of {var:[var, var...]} that lists for each variable,
			# the variables that it has a constraint on.
			# Each location in kenken puzzle is constrained on all other locations
			# in the same row and in the same column.
			# We are not adding same-cage members since that will be checked by constraints function
			for v in self.variables:
				self.neighbors[v] = list()
				(row, col) = self.variable_to_xy(v)

				for _ in range(self.N):
					if _ != row:
						# add all same column locations
						self.neighbors[v].append(self.xy_to_variable(_, col))

					if _ != col:
						# add all same row locations
						self.neighbors[v].append(self.xy_to_variable(row, _))


	# return the (i, j) corresponding to a variable.
	# For a board of N*N, variables range from 0 to N*N - 1
	# 0 -> (0, 0), N-1 -> (0, N-1), N -> (1, 0), ..., N*N-1 -> (N-1, N-1)
	def variable_to_xy(self, var):
		i = var // self.N
		j = var % self.N
		return (i, j)

	# convert (i, j) to variable - inverse of variable_to_xy
	def xy_to_variable(self, i, j):
		return i*self.N + j

	# which cage does this variable X belong to?
	def get_cage(self, X):
		(i, j)  = self.variable_to_xy(X)
		cage_id = self.cage_board[i][j]
		return self.cage_dict[cage_id]

	# return true if A=a and B=b don't violate any constraint,
	# false otherwise
	def constraints(self, A, a, B, b):
		assert A != B

		# if either variable A or B is in the same row/col as the other,
		# a must not be same as b
		if B in self.neighbors[A] and a == b:
			return False 
		if A in self.neighbors[B] and a == b:
			return False

		cage_A = self.get_cage(A)
		cage_B = self.get_cage(B)
		inferences = kenken_csp.infer_assignment()   # current assignments

		if cage_A == cage_B:
			# both belong to the same cage - need to check cage constraints for each operator
			if cage_A.opr == '+':
				return self.check_add_or_mul_cage(inferences, operator.add, A, a, B, b)
			elif cage_A.opr == '-':
				return abs(a - b) == cage_A.goal
			elif cage_A.opr == '*':
				return self.check_add_or_mul_cage(inferences, operator.mul, A, a, B, b)
			elif cage_A.opr == '/':
				return max(a, b) == min(a, b) * cage_A.goal
			elif cage_A.opr == '=':
				# this should never happen: '=' always has a single cage
				assert False
			else:
				print("unknown cage operator: %s" % cage_A.opr)
				assert False
		else:
			return self.check_cage_constraint(inferences, A, a) and self.check_cage_constraint(inferences, B, b)

	# check validity of an add or mul cage, with A=a and B=b (optional)
	def check_add_or_mul_cage(self, inferences, fn, A, a, B = None, b = None):
		allocated = 0
		cage = self.get_cage(A)
		total = (1 if fn == operator.mul else 0)

		for V in cage.vars:
			''' #if A (or B) is inferred, its value is a (or b)
			if V == A and V in inferences:
				assert a == inferences[V]
			if V == B and V in inferences:
				assert b == inferences[V]
			'''
			if V in inferences:
				total = fn(total, inferences[V])
				allocated += 1

		if total < cage.goal and allocated < len(cage.vars):
			# all variables are not allocated and current total is not reached too
			# ie, constraints are still ok
			return True
		elif total == cage.goal and allocated == len(cage.vars):
			# all variables are allocated and all variables are allocated
			return True
		return False

	# check validity of a sub or div cage, when X=x 
	def check_sub_or_div_cage(self, inferences, fn, X, x):
		cage = self.get_cage(X)

		# note - subtract or div cage only have 2 variables
		A, B = cage.vars[0], cage.vars[1]
		Y = (B if X != B else A)   # Y is the variable other than X in the same cage

		if Y in inferences:
			# if Y already has a value y, |x - y| or max(x,y) / min(x,y) must be cage.goal
			# for sub, this means max(x, y) == min(x, y) + goal
			# for div, this means max(x, y) == min(x, y) * goal
			y = inferences[Y]
			return max(x, y) == fn(min(x, y), cage.goal)
		else:
			# if Y is not inferred yet but has a possible value that will satisfy
			# cage goal, return true
			for y in kenken_csp.choices(Y):
				if max(x, y) == fn(min(x, y), cage.goal):
					return True
		return False

	# check if X=x keeps the cage it belongs to consistent
	def check_cage_constraint(self, inferences, X, x):
		cage = self.get_cage(X)
		if cage.opr == '+':
			return self.check_add_or_mul_cage(inferences, operator.add, X, x)
		elif cage.opr == '-':
			return self.check_sub_or_div_cage(inferences, operator.add, X, x)
		elif cage.opr == '*':
			return self.check_add_or_mul_cage(inferences, operator.mul, X, x)
		elif cage.opr == '/':
			return self.check_sub_or_div_cage(inferences, operator.mul, X, x)
		elif cage.opr == '=':
			return x == cage.goal
		else:
			print("unknown cage operator: %s" % cage.opr)
			assert False

	# display a kenken board   
	def print_result(self, assignment):
		if assignment:
			for i in range(self.N):
				for j in range(self.N):
					var = self.xy_to_variable(i, j)
					val = "_"
					if var in assignment:
						val = str(assignment[var])
					print("%2s" % val, end = " ")
				print()
		else:
			print("no solution found")

if __name__ == "__main__":
	if len(sys.argv) < 2:
		print("Insufficient arguments passed. Sample usage:\npython kenken.py <path-to-input-file>")
	filename = sys.argv[1]

	kenken     = Kenken(filename)
	kenken_csp = csp.CSP(kenken.variables, kenken.domains, kenken.neighbors, kenken.constraints)

	# 1. Basic backtracking
	print("1. Running basic backtracking ...")
	assignment1, node_count = csp.backtracking_search_with_assigment_count(kenken_csp)
	kenken.print_result(assignment1)
	print("(1) no. of assignments:", node_count)

	# 2. Improved backtacking: arc consistency (AC3) along with
	# minimum remaining heuristic and forward checking inference
	print("\n2. Improvement: AC3 along with mrv and forward_checking ...")

	# arc consistency AC3 algorithm as per text book.
	csp.AC3(kenken_csp)
	assignment2, node_count = csp.backtracking_search_with_assigment_count(kenken_csp, select_unassigned_variable=csp.mrv)
	kenken.print_result(assignment2)
	print("(2) no. of assignments: ", node_count)

	steps = 1000
	print("\n3. Local search (min min_conflicts - a hill climbing algorithm with %d max steps" % steps)
	assignment3, iterations = csp.min_conflicts_with_num_assignments(kenken_csp, max_steps = steps)
	kenken.print_result(assignment3)
	print("(3) no. of iterations:", iterations)

	print("\nDone")