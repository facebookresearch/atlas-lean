# Solvability of the stable paths problem is NP-complete

Deciding whether an instance of the [stable paths problem](the-stable-paths-problem.md) is solvable is NP-complete. Membership in NP: a path assignment can be guessed and its stability checked in polynomial time. Hardness: reduction from 3-SAT. Each variable $X_i$ gets a copy of DISAGREE on nodes $X_i$, $\bar X_i$ and the origin, whose two solutions encode $X_i$ true and false; each clause $C$ gets a node $C$ with three permitted paths $(C\,l\,0)$, one through each of its literals $l$, and a copy of BAD GADGET attached to $C$ that is solvable exactly when $C$ has a path to the origin. The resulting instance, polynomial in the size of the formula, is solvable if and only if the formula is satisfiable.

## Depends on

- [The stable paths problem](the-stable-paths-problem.md)

## Proof depends on

- [Stable paths problems can have several solutions or none](stable-paths-problems-can-have-several-solutions-or-none.md): DISAGREE has exactly two solutions and a cyclic gadget none.

## Sources

- T. G. Griffin, F. B. Shepherd and G. Wilfong, "The stable paths problem and interdomain routing", *IEEE/ACM Transactions on Networking* 10(2):232–243, 2002, Section V.A, Theorem V.1 with its proof (Figs. 7 and 8).
