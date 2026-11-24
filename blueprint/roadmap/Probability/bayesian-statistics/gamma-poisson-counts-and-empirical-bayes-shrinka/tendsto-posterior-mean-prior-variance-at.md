# No-shrinkage limit of the posterior mean

For every real `m`, `s > 0` and `k ∈ ℕ`, parametrize the Gamma prior by its mean `m` and variance
`v` (shape `m² / v`, rate `m / v`). Then the [posterior mean](posterior-mean.md)
`(m² / v + k) / (m / v + s)` tends to the per-cell estimate `k / s` as `v → ∞`. The limit holds for
every real `m` as an algebraic statement, but `Gamma(m² / v, m / v)` is a prior, and the expression
a posterior mean, only for `m > 0`.
