# To Stable E last Boundary Block

Evaluation of a single last-boundary block via `toStableE` equals the
stable elementary evaluation of its finite `n+1` representative.

Finite rank `n+1`, generic ring `R` (universe `u`), both orientations
`inl = column` and `inr = row`. Proved by cases on `b` and the private
`steinHomCol_eq_colStableHom` / `steinHomRow_eq_rowStableHom` chain,
reusing the existing finite block machinery.

Proves evaluation only; makes no pivot, scalar-equation, alternation,
kernel-generation, finite-stage landing, strict-decrease, cocycle,
naturality, or Matsumoto claim.
