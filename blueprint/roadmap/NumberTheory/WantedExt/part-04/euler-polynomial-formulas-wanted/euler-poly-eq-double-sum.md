---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.EulerPolynomialFormulasWanted.eulerPoly_eq_double_sum
---

# Theorem 4.3

**Theorem 4.3**: for every `n ≥ 0`,
`2^n E_n(x) = ∑_{ℓ=0}^n (-1)^ℓ / (ℓ + 1)
  ∑_{k=0}^{n-ℓ} ((k + ℓ + 1)! / 2^k) (ℓ + 1 choose k)
  S(n, k + ℓ, 2x - 1)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.EulerPolynomialFormulasWanted](../../../../../sources/v2/WantedExt.md)
- Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif, "Generalizations of Several Explicit Formulas for Euler Polynomials", Theorem 4.3.
