# To Stable E last Boundary Block list prod

Evaluation of a word of last-boundary blocks via `toStableE` equals the
stable elementary evaluation of the corresponding finite `n+1` elementary word.

Finite rank `n+1`, generic ring `R` (universe `u`), arbitrary word length,
both block orientations preserved pointwise. Proved by transparent list
induction using `toStableE_lastBoundaryBlock` and homomorphism laws
`map_mul` / `map_prod`.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim.
