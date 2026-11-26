# Trace Dist comm

Half-normalized trace distance is symmetric in the two matrices.

Here `n` is any finite index type. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceDist_comm (M N : Matrix n n ℂ) :
    traceDist M N = traceDist N M
```
