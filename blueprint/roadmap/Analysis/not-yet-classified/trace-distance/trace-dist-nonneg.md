# Trace Dist nonneg

Half-normalized trace distance between finite complex matrices is nonnegative.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_nonneg (M N : Matrix n n ℂ) :
    0 ≤ traceDist M N
```
