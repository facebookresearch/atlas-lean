# Last Boundary Block Elementary inl val

Coercion of the column (`inl`) elementary representative to
`Matrix.GeneralLinearGroup (Fin (n+1)) R` equals the public block
construction with `finSumFinEquiv` and `BlockElementary.upperUnit`.

Finite rank `n+1`, generic ring `R` (universe `u`), orientation
`inl = column = upper`. Right side uses only public names
(`reindexMulEquiv`, `finSumFinEquiv`, `BlockElementary.upperUnit`,
`Matrix.of`); no private `colMatrix`/`colEquiv`/`colGL` appears.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim.
