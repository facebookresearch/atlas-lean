# Generalized Rate

The rate function of a generalized current, `I(j_d) = inf {I(j) | j conservative with
∑_{y<z} d(y, z) j(y, z) = j_d}`, as a real infimum. It is meaningful only for feasible values
`x = j_d`, those attained by some conservative current: on an empty feasible set (for example
`d = 0` and `x ≠ 0`) the real infimum is the junk value `0`, whereas the rate function is `+∞`.
When `j_d^π ≠ 0` every real `x` is feasible (scale the stationary current `j^π`, which is
conservative), so the theorems below, which assume `j_d^π ≠ 0`, only concern feasible values;
`generalizedRate_le` also takes feasibility as an explicit hypothesis.
