# GEE asymptotic normality from differentiable cluster scores

The combination of
`linearization_of_hasFDerivAt` and `tendstoInDistribution_sqrt_smul_sub_sandwich`: if the cluster
scores are differentiable near `β₀`, their averaged Jacobian converges uniformly near `β₀` in
probability to a sensitivity function `Abar` continuous at `β₀` with `Abar β₀` invertible, the
estimator is a consistent root of the estimating equation with probability tending to one, and
the Lindeberg and meat hypotheses hold at `β₀`, then
`√n • (βhat n - β₀) → N(0, sandwichCovariance (Abar β₀) B)` in distribution.
