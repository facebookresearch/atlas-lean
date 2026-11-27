# Trace Dist def

The half-normalized trace distance is one-half the trace norm of the matrix difference.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_def (M N : Matrix n n ℂ) :
    traceDist M N = (1 / 2 : ℝ) * (M - N).traceNorm
```
