---
article_id: af_b8ec6a12cc93ba5f1ee6be57
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.LinearAlgebra.TraceNewtonWanted.LinearAlgebra.TraceNewton.charpolyDescendingCoeff
---

# Charpoly Descending Coeff

The coefficient `c_k` in the usual monic characteristic-polynomial
expansion `χ_A(X) = X^N + c₁ X^(N-1) + ... + c_N`.

Mathlib's `Matrix.charpoly` is the monic characteristic polynomial
`det (X • 1 - A)`, so this is the coefficient of degree `N - k`.
For `k > N`, the coefficient is `0`, which lets the trace recurrence be
stated uniformly for all positive `k`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.LinearAlgebra.TraceNewtonWanted](../../../../sources/v2/WantedExt.md)
