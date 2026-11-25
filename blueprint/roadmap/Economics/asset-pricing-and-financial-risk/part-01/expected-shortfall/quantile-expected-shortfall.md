# Expected shortfall as an integral of quantiles

For a loss `X` on a finite sample space with weights `p(ω)` and a level `α` (in use, `0 < α < 1`),
the quantile expected shortfall is `(1 - α)⁻¹ ∫_α^1 q_X(u) du`, where
`q_X(u) = inf {x : F_X(x) ≥ u}` for `0 < u < 1` (and `q_X(u) = 0` otherwise) is the lower quantile
of the [loss law](loss-law.md) and `F_X` its distribution function. For probability weights,
`p(ω) ≥ 0` with `∑_ω p(ω) = 1`, this gives the expected shortfall under `p`. The formula is
evaluated for all real weights, through the loss law (negative weights clamped to `0`), but for
other weights the loss law need not be a probability measure (one outcome of weight `2` has mass
`2`). With the convention `x / 0 = 0` it is `0` for `α = 1`.
