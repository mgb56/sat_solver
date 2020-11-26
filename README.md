# SAT Solver

An implementation of the CDCL SAT solver, using the DPLL algorithm and a search restart optimization. Input should be CNF version of the DIMACS format. 

Usage: python dpll.py <input_file>

Example usage: 
- python dpll.py bench/bench1/sat/10-25.cnf

Note: When running the test scripts, such as bench1.sh, dpll.py must be in the same directory as the scripts.