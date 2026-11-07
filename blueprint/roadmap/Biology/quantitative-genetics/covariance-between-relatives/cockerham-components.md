# Cockerham–Kempthorne variance components

Cockerham–Kempthorne variance components up to order `n`: `V i j = V_{A^i D^j}` is the
component of `i` additive and `j` dominance factors (`V 1 0 = V_A`, `V 0 1 = V_D`,
`V 2 0 = V_AA`, …). They are nonnegative, there is no `(0, 0)` component, and the genetic
covariance of relatives with `2φ` and `Δ` is `∑_{i, j ≤ n} (2φ)^i Δ^j V i j`. This structure
is the stated representation; it is proved for one locus by `LocusModel.relCov_eq`.
