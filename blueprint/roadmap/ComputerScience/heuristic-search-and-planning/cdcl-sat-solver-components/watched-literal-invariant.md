# Completeness of propagation with two watched literals

Maintain the invariant that for every clause $C$ with watches $\ell_1, \ell_2$ and no pending update (no conflict found, and $\neg\ell_1$ already processed from the propagation queue), if $\ell_1$ is false under the trail $M$ then $\ell_2$ is true at a decision level no higher than that of $\ell_1$; with blocker literals, "$\ell_2$" is weakened to "some literal of $C$". Then after all queued trail literals have been processed without a conflict, no clause of the database is unit or falsified under $M$. Hence propagation with two watched literals finds exactly the unit clauses and conflicts that a full scan of the database would find, while visiting only the watch lists of newly falsified literals; backjumping to a lower decision level preserves the invariant without any watch updates.

## Proof sketch

A clause whose two watches are not false is neither unit nor falsified, and a clause with a processed false watch contains a true literal. A visit restores the invariant: the clause gets a new non-false watch, or its other watch is (or is propagated) true at the current level, which is the level of $\ell_1$. Backjumping to level $b$ keeps every assignment of level at most $b$, so if $\ell_1$ stays false, the true literal of level at most that of $\ell_1$ stays true; otherwise $\ell_1$ is unassigned and the premise is void.

## Depends on

- [Two-watched-literal scheme](two-watched-literal-scheme.md)

## Sources

- M. Fleury, J. C. Blanchette and P. Lammich, "A Verified SAT Solver with Watched Literals Using Imperative HOL", Certified Programs and Proofs (CPP 2018), ACM, 2018, Sections 3 and 10: the invariant with the level condition and its compatibility with backjumping.
- M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang and S. Malik, "Chaff: Engineering an Efficient SAT Solver", Proceedings of the 38th Design Automation Conference, 2001.
- N. Eén and N. Sörensson, "An Extensible SAT-solver", Theory and Applications of Satisfiability Testing (SAT 2003), LNCS 2919, Springer, 2004.
