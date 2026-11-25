# Trace Norm nonneg

The finite complex matrix trace norm is nonnegative.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNorm_nonneg (M : Matrix n n ℂ) : 0 ≤ M.traceNorm
```
