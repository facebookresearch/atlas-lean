# Two-watched-literal scheme

In a clause database where every clause has at least two literals, the **two-watched-literal scheme** designates two distinct literals of each clause as its **watches** and keeps, for each literal $\ell$, a watch list of the clauses watching $\ell$, each entry paired with a **blocker** literal of the clause. When $\ell$ becomes false under the current trail, only the clauses on the watch list of $\ell$ are visited: an entry whose blocker is true is skipped; otherwise, if the other watch is true the clause is left as it is; else, if some unwatched literal is not false, it replaces $\ell$ as a watch (and the clause moves to that literal's watch list); else the clause is unit on its other watch if that watch is unassigned (which is then propagated), or falsified (a conflict) if it is false. Watches are not changed on backjumping. Blockers are an optimization of the original scheme of Chaff.

## Depends on

- [Abstract DPLL with learning](../../../Logic/propositional-logic/sat-solving/abstract-dpll-with-learning.md)
- [CNF formula](../../../Logic/propositional-logic/conjunctive-normal-form/cnf.md)

## Sources

- M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang and S. Malik, "Chaff: Engineering an Efficient SAT Solver", Proceedings of the 38th Design Automation Conference, 2001.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
- G. Chu, A. Harwood and P. J. Stuckey, "Cache Conscious Data Structures for Boolean Satisfiability Solvers", Journal on Satisfiability, Boolean Modeling and Computation 6, 2009: blocker literals.
- M. Fleury, J. C. Blanchette and P. Lammich, "A Verified SAT Solver with Watched Literals Using Imperative HOL", Certified Programs and Proofs (CPP 2018), ACM, 2018, Section 3: the four cases of a watch-list visit.
