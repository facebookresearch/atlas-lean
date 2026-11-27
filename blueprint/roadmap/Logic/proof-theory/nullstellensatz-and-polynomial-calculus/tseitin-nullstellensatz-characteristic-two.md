# Tseitin formulas are easy for Nullstellensatz in characteristic two

Over a ring of characteristic $2$, if every vertex of a multigraph $G$ has at most $k$ non-loop incident edges and the total charge is odd, then the clause polynomials of the Tseitin formula $T(G,\chi)$ have a Nullstellensatz refutation of degree $k$ with all multipliers equal to $1$, without using the Boolean axioms and without connectivity assumptions.

## Proof sketch

In characteristic two the clause polynomials of the parity constraint at $v$ sum to $[\chi(v) = 1] + \sum_{e \ni v} x_e$; summing over all vertices each edge variable appears twice and cancels, leaving the total charge $1$.

## Depends on

- [Tseitin formulas of a multigraph](../tseitin-formulas/tseitin-formulas-of-a-multigraph.md)
- [Nullstellensatz proofs and degree](nullstellensatz-proofs.md)

## Sources

- S. Buss, D. Grigoriev, R. Impagliazzo and T. Pitassi, "Linear Gaps between Degrees for the Polynomial Calculus Modulo Distinct Primes", Journal of Computer and System Sciences 62(2), 267–289, 2001.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.5.3 (Tseitin formulas are easy over GF(2)).
- D. Grigoriev, "Tseitin's Tautologies and Lower Bounds for Nullstellensatz Proofs", Proceedings of the 39th IEEE Symposium on Foundations of Computer Science (FOCS), 1998.
