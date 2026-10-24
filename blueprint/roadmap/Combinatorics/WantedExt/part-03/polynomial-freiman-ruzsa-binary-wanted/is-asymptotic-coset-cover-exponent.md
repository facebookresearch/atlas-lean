---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted.IsAsymptoticCosetCoverExponent
---

# Is Asymptotic Coset Cover Exponent

`C` is an admissible asymptotic coset-cover exponent.  The
`∀ ε > 0, ∃ K₀, ∀ K ≥ K₀` prefix is the source's uniform
`K^(C + o(1))` convention: after `K` is sufficiently large, the same
bound works in every dimension and for every nonempty doubling set.

`CovByVAdd` is Mathlib's concrete finite-coset-cover predicate.  Thus the
conclusion supplies an actual linear subspace and an actual finite set of
translates, rather than a caller-provided cover oracle.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Binary Ambient Space](binary-ambient-space.md)

## Sources

- [WantedExt, WantedExt.Combinatorics.PolynomialFreimanRuzsaBinaryWanted](../../../../../sources/v2/WantedExt.md)
- Optimization Problems constant 18a, with the uniform asymptotic quantifiers made explicit.
