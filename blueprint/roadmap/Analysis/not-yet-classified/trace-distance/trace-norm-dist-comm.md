# Trace Norm Dist comm

Full trace distance is symmetric in the two matrices.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNormDist_comm (M N : Matrix n n ℂ) :
    traceNormDist M N = traceNormDist N M
```
