# Trace Dist self

The half-normalized trace distance from a matrix to itself is zero.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_self (M : Matrix n n ℂ) :
    traceDist M M = 0
```
