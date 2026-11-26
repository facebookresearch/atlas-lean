# Trace Norm Dist def

The full trace distance is the trace norm of the matrix difference.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_def (M N : Matrix n n ℂ) :
    traceNormDist M N = (M - N).traceNorm
```
