# Trace Norm Dist self

The full trace distance from a matrix to itself is zero.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_self (M : Matrix n n ℂ) :
    traceNormDist M M = 0
```
