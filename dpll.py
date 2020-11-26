# Data structures:
#				   unit_prop: Stores whether each var (or their negation) has been deduced
#							  (name isn't very accurate. should be called assignments or something)				
#			  decision_stack: Stack of vars that have been decided
#			decision_visited: Set of vars that have been decided at some point
#	unit_prop_after_decision: Dict from decision var to values that have been deduced since
#							  each var was decided

# Var representation:
#	Represent each of n vars as an element in a list. 
#	In clauses, a value of 0 means the var is not part of the clause.
#	A value of 1 means the var appears in the clause, while -1 means the negation is in the clause.
#
#	In unit_prop, 0 means the literal is not yet assigned. 1 means the var has been deduced.
#	-1 means the negation of the var has been deduced.

# Algorithm:
#	While we can backtrack or a literal has not been assigned yet
#		Backtrack if all literals have been assigned
#		else unit_prop if we can do so and decide if we can't
#
#		if assignment is SAT then print solution and return
#
#	print UNSAT and return

# Extension - randomized search restart
#	randomize clause ordering and variable and value selection 
#	restart search after a certain number of backtracks, with increasing cutoffs

import sys
import os
import random

# @return: whether clauses are currently sat or not
def is_sat(clauses, unit_prop):

	# to check SAT, need to check if clause[i] == unit_prop[i]
	for clause in clauses:
		clause_is_sat = False
		for i, _ in enumerate(clause):
			if clause[i] == unit_prop[i] and clause[i] != 0:
				clause_is_sat = True
				break
	 		
		if not clause_is_sat:
	 		return False

	return True


# @param nvar: number of variables specified in DIMACS input
# @param clauses: list of clauses from DIMACS input
# @return clauses: clauses converted into internal representation
def create_clauses(nvar, clauses):
	clses = []

	for clause in clauses:
		new_clause = [0] * nvar
		for num in clause:
			if num == 0:
				break

			new_clause[abs(num) - 1] = 1 if num > 0 else -1

		clses.append(new_clause)

	return nvar, clses


# @param unit_prop: values assigned for variables (or initially sat if 0) 
# @return: none
def print_sat(clauses, unit_prop):
	print("sat", end="")
	for i, num in enumerate(unit_prop):
		if num == 0:
			continue

		if num == 1:
			print(" " + str(i+1), end="")
		else:
			print(" " + "-" + str(i+1), end="")

	print()
	return


# @param unit_prop: values assigned for variables (or initially sat if 0) 
# @return bool: whether the clause should be unit_prop'd
def should_unitprop(clause, unit_prop, var_order):
	num_vars = 0
	idx = []

	for i in var_order:
		if clause[i] != 0:
			num_vars += 1
			idx.append(i)

	num_false = 0
	num_true = 0
	idx_prop = -1
	for i in var_order:
		if unit_prop[i] != 0 and clause[i] != 0 and unit_prop[i] != clause[i]: 
			num_false += 1
		elif unit_prop[i] != 0 and clause[i] != 0:
			num_true += 1
		elif i in idx and unit_prop[i] == 0:
			idx_prop = i

	return num_vars - num_false == 1 and num_true == 0, idx_prop


# @return: sat or unsat
def dpll(nvar, clauses):

	unit_prop = [0] * nvar
	# holds the index of the decision variables. can be used with unit_prop to backtrack
	decision_stack = []
	decision_visited = set()

	# these two pieces of data keep track of values need to be reset in unitprop after backtrack
	unitprop_after_decision = {}
	last_decision = None


	# data for search restarts
	var_order = list(range(len(clauses[0])))
	backtrack_count = 0
	restart_cutoff = 4

	while decision_stack or 0 in unit_prop:

		if not decision_stack and 0 not in unit_prop:
			break

		# search restart
		if backtrack_count >= restart_cutoff:

			# prepare counts for next restart
			backtrack_count = 0
			restart_cutoff *= 2

			# randomize variable selection
			random.shuffle(var_order)

			# reset data structures
			unit_prop = [0] * nvar
			decision_stack = []
			decision_visited = set()
			unitprop_after_decision = {}
			last_decision = None
			continue


		# try backtrack
		elif 0 not in unit_prop:

			backtrack_idx = decision_stack.pop()

			if unit_prop[backtrack_idx] == 0:
				raise NotImplementedError
			
			unit_prop[backtrack_idx] *= -1

			decision_visited.add(backtrack_idx)

			for idx in unitprop_after_decision[backtrack_idx]:
				unit_prop[idx] = 0

			backtrack_count += 1

		# extend assignment
		else:

			clause_to_unitprop = None
			idx_to_unitprop = -1 
			for clause in clauses:
				should_prop, idx = should_unitprop(clause, unit_prop, var_order)
				if should_prop:
					clause_to_unitprop = clause
					idx_to_unitprop = idx
					break

			# should unitprop
			if clause_to_unitprop:
				unit_prop[idx_to_unitprop] = clause_to_unitprop[idx_to_unitprop]

				if last_decision:
					unitprop_after_decision[last_decision].append(idx_to_unitprop)

			else:

				# guess decision value
				idx_to_decide = -1
				for i, num in enumerate(unit_prop):
					if num == 0 and i not in decision_visited:
						idx_to_decide = i
						break

				if idx_to_decide != -1:

					# randomize decision value
					unit_prop[idx_to_decide] = random.choice([-1, 1])
					decision_stack.append(idx_to_decide)
					unitprop_after_decision[idx_to_decide] = []
					last_decision = idx_to_decide


		if is_sat(clauses, unit_prop):
			print_sat(clauses, unit_prop)
			return

	print("unsat")



def main():	
	if len(sys.argv) != 2 or sys.argv[0] != "dpll.py":
		sys.exit("Usage: python dpll.py <input_file>")

	script_dir = os.path.dirname(__file__)
	abs_file_path = os.path.join(script_dir, sys.argv[1])
	with open(abs_file_path) as myFile:
		program = myFile.read()
		program = program.split("\n")

		if program[-1] == '':
			program = program[:-1]

		form = program[0].split()
		nvar = int(form[2])

		clauses = []
		for i in range(1, len(program)):
			clauses.append([int(num) for num in program[i].split()])


		nvar, clauses = create_clauses(nvar, clauses)
		print("nvar is", nvar)
		print("clauses is", clauses)
		print()
		dpll(nvar, clauses)


if __name__ == '__main__':
	main()

