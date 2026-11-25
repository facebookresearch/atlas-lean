# Block Diagonal One reindex

For a semiring `R`, finite types `A`, `A'`, `I`, `I'` with decidable
equality, equivalences `eA : A ≃ A'`, `eI : I ≃ I'`, and `g : GL A R`, reindexing
`blockDiagonalOne A I R g` by `Equiv.sumCongr eA eI` gives
`blockDiagonalOne A' I' R (reindexMulEquiv eA g)`. The reindexing permutes the inactive
identity block without changing it.
