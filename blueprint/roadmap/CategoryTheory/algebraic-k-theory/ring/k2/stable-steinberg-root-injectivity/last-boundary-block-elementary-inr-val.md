# Last Boundary Block Elementary inr val

Coercion of the row (`inr`) elementary representative to
`Matrix.GeneralLinearGroup (Fin (n+1)) R` equals the public block
construction with `finSumFinEquiv` and `BlockElementary.lowerUnit`.

Finite rank `n+1`, generic ring `R` (universe `u`), orientation
`inr = row = lower`. Right side uses only public names
(`reindexMulEquiv`, `finSumFinEquiv`, `BlockElementary.lowerUnit`,
`Matrix.of`); no private `rowMatrix`/`colEquiv`/`rowGL` appears.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim.
