# Executable full-LTL model checker

The model-checking procedure for full LTL on a labelled transition system with a set of initial
states: it returns `true` exactly when the product of the system with the Büchi automaton of the
negated formula accepts no infinite run, which it decides by a reachability search. To run, it needs finitely many states and actions, decidable equality of states, and decidable
transitions, initial states and valuation; these are needed to run the procedure, not to state
what it decides.
