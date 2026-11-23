# No-shrinkage limit, posterior mean

Parametrize the Gamma prior by its mean `m` and
variance `v` (shape `m² / v`, rate `m / v`). As the prior variance `v → ∞` the posterior mean
tends to the per-cell estimate `k / s`. The limit holds for every real `m` as an algebraic
statement, but `Gamma(m² / v, m / v)` is a prior (and `posteriorMean` a posterior mean) only for
`0 < m`.
