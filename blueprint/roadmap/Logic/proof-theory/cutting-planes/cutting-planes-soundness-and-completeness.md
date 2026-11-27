# Soundness and refutation completeness of cutting planes

Every line derived in cutting planes from a system $\Gamma$ of integer linear inequalities holds at every $0/1$ solution of $\Gamma$, so a refutable system has no $0/1$ solution. Conversely every finite system $\Gamma$ without a $0/1$ solution has a cutting planes refutation, possibly of exponential size. In particular a CNF formula is unsatisfiable iff the cutting-planes translation of its clauses is refutable.

## Proof sketch

Rounding is sound because the left side is an integer at $0/1$ points. Completeness for general systems is Chvátal's theorem that finitely many rounds of Chvátal–Gomory cuts reach the integer hull, which is empty here; for CNF formulas it also follows from the simulation of resolution together with refutation completeness of resolution.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)

## Proof depends on

- [Cutting planes polynomially simulate resolution](cutting-planes-simulate-resolution.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.6.1.
- V. Chvátal, "Edmonds Polytopes and a Hierarchy of Combinatorial Problems", Discrete Mathematics 4(4), 305–337, 1973.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
