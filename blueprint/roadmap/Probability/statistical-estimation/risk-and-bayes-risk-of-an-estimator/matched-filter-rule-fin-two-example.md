# `n = 2`, non-diagonal covariance, all three branches

`R = [[2, 1], [1, 2]]`,
`s0 = 0`, `s1 = (1, 1)`, equal priors, zero-one costs: `R⁻¹ s1 = (1/3, 1/3)`, the statistic is
`(y₁ + y₂) / 3` and the threshold `log 1 + (2/3) / 2 = 1/3`. The rule decides `true` at
`(1, 1)`, `tie` at `(1, 0)` and `false` at `(0, 0)`.
