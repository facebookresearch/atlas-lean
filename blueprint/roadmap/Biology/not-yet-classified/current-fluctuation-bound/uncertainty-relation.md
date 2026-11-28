# Thermodynamic uncertainty relation, curvature form

**Thermodynamic uncertainty relation, curvature form** (Gingrich et al. 2016, Eq. (8)). In
the setting `Setting r π` (an ergodic chain and its stationary law `π`), let `d` be a weight with
`j_d^π ≠ 0` (so every `x` is feasible and the rate `I(j_d = x)` is finite; the real-valued rate
function is `x ↦ (I(j_d = x)).toReal`), and suppose
this real rate function is differentiable near `j_d^π` and its derivative has derivative
`c = I''(j_d^π) > 0` at `j_d^π`. Then the reciprocal curvature satisfies
`(1 / I''(j_d^π)) Σ^π / (j_d^π)² ≥ 2`, i.e. `I''(j_d^π) ≤ Σ^π / (2 (j_d^π)²)`. This is a
statement about the large-deviation rate function. The source reads `1 / I''(j_d^π)` as the
asymptotic variance `Var(j_d)` of the time-averaged current (the second-order expansion of the
rate function at its minimum), which gives the stochastic uncertainty relation
`Var(j_d) Σ^π / (j_d^π)² ≥ 2`; that identification, a consequence of the large deviation
principle, is not stated here.

## Sources

- Gingrich, Horowitz, Perunov and England (2016), Eq. (8).
