# Coe stabilization

For a semiring `R`, `n : ℕ`, and `g : GL (Fin n) R`, the underlying
matrix of `stabilization R g` is `fromBlocks ↑g 0 0 1` reindexed on both axes by
`finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)`.
