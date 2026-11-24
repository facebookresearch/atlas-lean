# Conditional decay at a branch point with a Hurwitz Jacobian

For the current
`I = I∞(V)` there are `δ, K, α > 0` such that every solution of the squid system on `[0, ∞)`
starting within `δ` of `eqPoint V` satisfies `‖x t - eqPoint V‖ ≤ K e^{-α t} ‖x 0 - eqPoint V‖`.
Like `LinearizedStability.globalSolution_decay_of_hasFDerivAt`, which it specializes, this does
not assert that such solutions exist, so it is not by itself local exponential stability.
