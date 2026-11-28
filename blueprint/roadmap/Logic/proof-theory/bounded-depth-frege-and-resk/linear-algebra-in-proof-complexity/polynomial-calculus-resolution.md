# Distinct-monomial size of PCR refutations

The distinct-monomial size of a [polynomial calculus with resolution](../../algebraic-and-semialgebraic-proof-systems/polynomial-calculus.md) ($\mathrm{PCR}_{\mathbb F}$) refutation counts the number of distinct monomials appearing across all lines of the refutation, as used in the weak-rank lower bounds of Garlík, Gryaznov, Ren and Tzameret.

Take $\mathrm{PCR}_{\mathbb F}$ refutations, twin variables $\bar x_i$, Boolean and complementarity axioms, degree, and CNF clause encodings from [Polynomial calculus](../../algebraic-and-semialgebraic-proof-systems/polynomial-calculus.md). In contrast to monomial size counted with repetitions, the **distinct-monomial size** of a $\mathrm{PCR}_{\mathbb F}$ refutation is the number of distinct monomials appearing in its lines (counted without repetitions across lines).

## Expansion

Counting distinct monomials is never larger than counting monomials with repetitions, so a lower bound on distinct-monomial size implies the same lower bound under the repetition-counted size of [Polynomial calculus](../../algebraic-and-semialgebraic-proof-systems/polynomial-calculus.md). Lower bounds in this size measure include those for the [weak rank principle](weak-rank-pcr-f2-lower-bounds.md) and its [perfect matching encoding](weak-rank-perfect-matching-lower-bounds.md).

## Depends on

- [Polynomial calculus](../../algebraic-and-semialgebraic-proof-systems/polynomial-calculus.md)

## Proof depends on

None.

## Sources

- Michal Garlík, Svyatoslav Gryaznov, Hanlin Ren and Iddo Tzameret, "The Weak Rank Principle: Lower Bounds and Applications", *58th Annual ACM Symposium on Theory of Computing (STOC 2026)*, 2026, https://doi.org/10.1145/3798129.3800735; numbering as in arXiv:2608.08760v1 (Section 2.1, remark after Theorem 2.1 reading size as the number of distinct monomials appearing in the refutation; Section 4.2, Definition 4.3 and Definition 4.5).
