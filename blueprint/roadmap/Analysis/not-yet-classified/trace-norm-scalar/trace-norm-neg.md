# Trace Norm neg

Negating a finite square complex matrix preserves its trace norm.
The index type is finite with decidable equality, and an empty index type
or zero matrix is included.

```lean
theorem traceNorm_neg (M : Matrix n n ℂ) :
    (-M).traceNorm = M.traceNorm
```
