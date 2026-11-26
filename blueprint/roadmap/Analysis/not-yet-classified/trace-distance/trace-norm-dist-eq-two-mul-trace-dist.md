# Trace Norm Dist eq two mul trace Dist

The full trace distance is exactly twice the half-normalized trace distance.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_eq_two_mul_traceDist (M N : Matrix n n ℂ) :
    traceNormDist M N = 2 * traceDist M N
```
