# Coe reindex Mul Equiv

For a semiring `R`, finite index types `n`, `m` with decidable equality,
`e : n ≃ m`, and `g : GL n R`, the underlying matrix of `reindexMulEquiv e g` is
`Matrix.reindex e e ↑g`: entry `(i, j)` is `g (e.symm i) (e.symm j)`.
