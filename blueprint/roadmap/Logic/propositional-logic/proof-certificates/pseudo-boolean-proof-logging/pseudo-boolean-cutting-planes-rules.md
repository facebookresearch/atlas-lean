# Pseudo-Boolean cutting planes with saturation and weakening

On normalized pseudo-Boolean constraints the rules of pseudo-Boolean cutting planes are: *literal axioms* $\ell \ge 0$; *addition* of two constraints followed by normalization (a term $a x + b \bar x$ becomes $(a-b) x + b$ moved into the degree, or symmetrically); *multiplication* by a positive integer; *division* by $c > 0$ rounding coefficients and degree up; *saturation*, replacing every coefficient $a_i > d$ by $d$; and *weakening*, deleting a term $a_i \ell_i$ and decreasing the degree by $a_i$. All rules are sound for $0/1$ assignments; weakening is shorthand for adding a multiple of a literal axiom, while saturation, like division, is sound only for integral solutions and is not one of the standard cutting planes rules.

## Depends on

- [Pseudo-Boolean constraints in normalized form](pseudo-boolean-constraints.md)
- [The cutting planes proof system](../../../proof-theory/cutting-planes/cutting-planes-proof-system.md)

## Sources

- B. Bogaerts, S. Gocht, C. McCreesh and J. Nordström, "Certified Dominance and Symmetry Breaking for Combinatorial Optimisation", Journal of Artificial Intelligence Research 77, 1539–1589, 2023.
- S. Gocht and J. Nordström, "Certifying Parity Reasoning Efficiently Using Pseudo-Boolean Proofs", Proceedings of the 35th AAAI Conference on Artificial Intelligence, 2021.
- S. Buss and J. Nordström, "Proof Complexity and SAT Solving", in Handbook of Satisfiability, 2nd ed., IOS Press, 2021, Section 7.6.1 (rules (7.27a)–(7.27d), (7.36a)–(7.36b)).
