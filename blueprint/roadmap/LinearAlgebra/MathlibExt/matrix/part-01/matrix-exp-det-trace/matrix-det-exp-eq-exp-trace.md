---
article_id: af_6011dac3110bb354fed891db
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted.matrix_det_exp_eq_exp_trace
---

# Matrix det exp eq exp trace

Jacobi's formula: the determinant of the matrix exponential is the exponential of the trace.

Proof: the three cases of B. C. Hall, An Elementary Introduction to Groups and Representations,
https://arxiv.org/abs/math-ph/0005032, Theorem 3.10. The Jordan-Chevalley decomposition
(`Module.End.exists_isNilpotent_isSemisimple`) writes `A = N + S` with `N` nilpotent, `S`
semisimple and `N`, `S` commuting, so `exp A = exp N * exp S`. Diagonalizing `S` gives
`det (exp S) = exp (trace S)`. For the nilpotent part, where Hall uses a strictly upper-triangular
form, `exp N - 1` is nilpotent, so `det (exp N) = 1`, while `trace N = 0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTrace](../../../../../../sources/v2/MathlibExt.md)
- Mathlib `docs/undergrad.yaml`, Linear algebra / Exponential / matrix exponential; B. C. Hall, Lie Groups, Lie Algebras, and Representations, 2nd ed., Springer (2015), Proposition 2.23.
