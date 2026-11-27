# Trace Dist eq half trace Norm Dist

The half-normalized trace distance is exactly one-half the full trace distance.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_eq_half_traceNormDist (M N : Matrix n n ℂ) :
    traceDist M N = (1 / 2 : ℝ) * traceNormDist M N
```
