# Cutting planes are exponentially stronger than resolution

Resolution does not polynomially simulate cutting planes: the formulas $\mathrm{PHP}^{n+1}_n$ have cutting planes refutations with $O(n^3)$ lines, while every resolution refutation has $2^{\Omega(n)}$ lines. Combined with the simulation of resolution by cutting planes, cutting planes is strictly stronger than resolution.

## Proof sketch

Combine the polynomial-size cutting planes refutation with Haken's lower bound for resolution.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Pigeonhole formulas $\mathrm{PHP}^m_n$](../resolution-lower-bounds/pigeonhole-formulas.md)

## Proof depends on

- [Polynomial-size cutting planes refutations of the pigeonhole principle](cutting-planes-refute-pigeonhole.md)
- [Cutting planes polynomially simulate resolution](cutting-planes-simulate-resolution.md)
- [Haken's lower bound for the pigeonhole principle](../../propositional-logic/propositional-proof-complexity/haken-s-lower-bound-for-the-pigeonhole-principle.md)

## Sources

- W. Cook, C. R. Coullard and Gy. Turán, "On the Complexity of Cutting-Plane Proofs", Discrete Applied Mathematics 18(1), 25–38, 1987.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.7.2.
- A. Haken, "The Intractability of Resolution", Theoretical Computer Science 39, 297–308, 1985.
- S. Jukna, Boolean Function Complexity: Advances and Frontiers, Springer, 2012.
