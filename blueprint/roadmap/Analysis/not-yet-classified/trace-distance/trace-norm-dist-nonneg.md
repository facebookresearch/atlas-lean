# Trace Norm Dist nonneg

Full trace distance between finite complex matrices is nonnegative.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_nonneg (M N : Matrix n n ℂ) :
    0 ≤ traceNormDist M N
```
