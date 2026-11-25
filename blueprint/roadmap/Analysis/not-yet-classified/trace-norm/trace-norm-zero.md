# Trace Norm zero

The zero matrix has trace norm zero.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNorm_zero : (0 : Matrix n n ℂ).traceNorm = 0
```
