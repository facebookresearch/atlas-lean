---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.ModInverseSwitchingWanted.euclid_bezout_coeffs_leastAbsInverse
---

# Lemma 4

**Lemma 4**: the pair `(s₂, s₁)` of Bézout coefficients
provided by the Euclidean algorithm for `(m, n)` (where
`r₀ = m/gcd(m,n)`, `r₁ = n/gcd(m,n)`) satisfies
`s₂ m + s₁ n = gcd(m, n)`, the coefficient `s₂` of `m` is the
least absolute inverse of `m/gcd(m,n)` modulo `n/gcd(m,n)`, and
the coefficient `s₁` of `n` is the least absolute inverse of
`n/gcd(m,n)` modulo `m/gcd(m,n)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ModInverseSwitchingWanted](../../../../../sources/v2/WantedExt.md)
- Spiros Konstantogiannis, "The Euclidean Algorithm as a Sequence of Modular Inverse Switching Formulas", Lemma 4.
