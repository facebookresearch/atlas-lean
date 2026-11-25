# Block Diagonal Hom sum Assoc

For a semiring `R`, finite index types `α`, `β`, `γ` with decidable
equality, and `g : GL α R`, `h : GL β R`, `k : GL γ R`, the two iterated block maps satisfy
`reindexMulEquiv (Equiv.sumAssoc α β γ)
  (blockDiagonalHom (α ⊕ β) γ R (blockDiagonalHom α β R (g, h), k))
= blockDiagonalHom α (β ⊕ γ) R (g, blockDiagonalHom β γ R (h, k))`.
The reindexing sends `(α ⊕ β) ⊕ γ` to `α ⊕ (β ⊕ γ)`, preserving the order of the blocks.
