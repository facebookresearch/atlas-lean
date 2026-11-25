# Generalized Rate

The rate function of a generalized current, `I(j_d = x) = inf {I(j) | j conservative with
∑_{y<z} d(y, z) j(y, z) = x}`, with values in `[0, ∞]`. On an infeasible value `x`, attained by no
conservative current (for example `d = 0` and `x ≠ 0`), the infimum is over the empty set and the
rate is `+∞`. When `j_d^π ≠ 0` every real `x` is feasible (scale the stationary current `j^π`,
which is conservative), and the rate is finite by `generalizedRate_le`.
