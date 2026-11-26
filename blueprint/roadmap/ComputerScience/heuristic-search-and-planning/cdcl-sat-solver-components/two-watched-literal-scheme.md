# Two-watched-literal scheme

In a clause database where every clause has at least two literals, the **two-watched-literal scheme** designates two distinct literals of each clause as its **watches** and keeps, for each literal $\ell$, a watch list of the clauses watching $\ell$, each entry paired with a **blocker** literal of the clause. When $\ell$ becomes false under the current trail, only the clauses on the watch list of $\ell$ are visited: an entry whose blocker is true is skipped; otherwise the clause either finds a non-false replacement watch (and moves to its watch list), is satisfied by its other watch, becomes unit on its other watch, or is falsified (a conflict).

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)
- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang and S. Malik, "Chaff: Engineering an Efficient SAT Solver", Proceedings of the 38th Design Automation Conference, 2001.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
