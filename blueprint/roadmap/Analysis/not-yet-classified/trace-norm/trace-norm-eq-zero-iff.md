# Trace Norm eq zero iff

A finite complex matrix has trace norm zero exactly when it is the zero matrix.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_eq_zero_iff (M : Matrix n n ℂ) :
    M.singularValueTraceNorm = 0 ↔ M = 0
```
