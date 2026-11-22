# Executable LTL satisfiability test

For a finite alphabet and a decidable valuation, this Boolean runs the Büchi emptiness test on
the automaton of the formula, which has at most $4^{|\varphi|}$ states, and returns `true` when
the automaton is nonempty. No running time is proved.
