# Trace Dist eq zero iff

Half-normalized trace distance is zero exactly when the matrices are equal.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_eq_zero_iff (M N : Matrix n n ℂ) :
    traceDist M N = 0 ↔ M = N
```
