# Soundness and refutation completeness of cutting planes

Every line derived in cutting planes from a system $\Gamma$ of integer linear inequalities holds at every $0/1$ solution of $\Gamma$, so a refutable system has no $0/1$ solution. Conversely every system $\Gamma$ (possibly infinite, over any set of variables) without a $0/1$ solution has a cutting planes refutation, possibly of exponential size. In particular a CNF formula is unsatisfiable iff the cutting-planes translation of its clauses is refutable.

## Proof sketch

Rounding is sound because the left side is an integer at $0/1$ points. Completeness follows by eliminating variables one at a time: from a refutation of the systems with $x_v$ fixed to $0$ and to $1$, derive $x_v \ge 1$ and $-x_v \ge 0$-type inequalities weakened by large multiples of the axioms, and combine them.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- V. Chvátal, "Edmonds Polytopes and a Hierarchy of Combinatorial Problems", Discrete Mathematics 4(4), 305–337, 1973.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
