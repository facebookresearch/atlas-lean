---
article_id: af_f7c56f43b36c504b0f9bc051
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.irreducible_of_dumas_padic_criterion
---

# Dumas Irreducibility Criterion

Dumas irreducibility criterion, integer-polynomial specialization.

For `f = Σ A_i x^i ∈ ℤ[x]` with `A₀ Aₙ ≠ 0`, if its Newton polygon for a prime
is a single segment with no lattice points except endpoints, then `f` is irreducible.
This is the exact one-edge/no-interior-lattice-points algebraic form:
`a₀aₙ ≠ 0`, `gcd(v_p(a₀) - v_p(aₙ), n) = 1` via no divisibility by any `k > 1`
dividing `n`, and the Newton-polygon line inequality
`n v_p(a_i) ≥ (n - i) v_p(a₀) + i v_p(aₙ)` for `0 ≤ i ≤ n`.
The source valuation convention is extended with `v(0) = ∞`; since Mathlib's
`padicValRat p 0 = 0`, the inequality is stated only under `f.coeff i ≠ 0`,
which is exactly omission of zero-coefficient points, not a weakening.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Polynomial.DumasIrreducibilityCriterion](../../../../../sources/v2/MathlibExt.md)
- Randell Heyman, *On the Number of Polynomials of Bounded Height that Satisfy the Dumas Criterion*, Journal of Integer Sequences 17 (2014), Article 14.2.4, Dumas criterion statement (label `f(x)`), lines 96–102, <https://cs.uwaterloo.ca/journals/JIS/VOL17/Heyman/heyman2.tex>. Exact algebraic form: Martin Juras, arXiv:1505.07633v1, lines 67–100. Proves `Wanted` entry `irreducible_of_dumas_padic_criterion`.
