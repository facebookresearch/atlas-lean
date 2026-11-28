# Generalized Rate

The rate function of a generalized current, `I(j_d = x) = inf {I(j) | j conservative with
∑_{y<z} d(y, z) j(y, z) = x}`, with values in `[0, ∞]`. On an infeasible value `x`, attained by no
conservative current (for example `d = 0` and `x ≠ 0`), the infimum is over the empty set and the
rate is `+∞`. In the setting `Setting r π`, where `π` is stationary, `j_d^π ≠ 0` makes every real
`x` feasible (scale the stationary current `j^π`, which stationarity makes conservative), and the
rate is then finite by `generalizedRate_le`. A nonzero `j_d^p` for a law `p` that is not
stationary gives neither: with two states, unit rates both ways, `d = 1` and `p = (3/4, 1/4)`,
`j^p ≠ 0`, yet the only conservative current is `0`, so the rate at `x = 1` is `+∞`.
