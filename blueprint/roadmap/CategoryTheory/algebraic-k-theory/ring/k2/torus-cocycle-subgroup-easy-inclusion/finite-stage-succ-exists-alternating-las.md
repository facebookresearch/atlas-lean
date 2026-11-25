# Finite Stage succ exists alternating last Boundary Blocks

Every `g ∈ finiteStage (n+1)` has an adjacent-alternating boundary-block list
representation with `List.IsChain BoundaryBlocksAlternate` (i.e. adjacent sides
differ). Uses `finiteStage_succ_exists_lastBoundaryBlocks` and
`normalizeBoundaryBlocks` which merges only adjacent same-side blocks via
`lastBoundaryBlock_inl_mul_inl` / `inr_mul_inr`, preserving exact product order.
Termination by `length`. The statement is the sound adjacent-alternating property:
it explicitly does not claim `List.Pairwise`, length ≤ 2, arbitrary zero-forcing,
or full kernel generation. No equal-index factorization beyond the `Fin 1`
kernel lemmas is used.
