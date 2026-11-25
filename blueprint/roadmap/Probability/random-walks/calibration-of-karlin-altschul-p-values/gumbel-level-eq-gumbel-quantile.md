# The Gumbel level is the Gumbel quantile at one minus the level

For `K > 0`, `0 < α < 1` and every real `θ`, the [Gumbel level](gumbel-level.md) is
`x_α = μ - β log(-log(1 - α))` with `μ = log K / θ` and `β = θ⁻¹`; when `θ = 0` both sides are `0`,
by the conventions `x / 0 = 0` and `0⁻¹ = 0`. For `θ > 0` the right side is the `(1 - α)`-quantile
of the Gumbel law with location `μ` and scale `β`, whose distribution function is
[`exp(-K e^{-θ x})`](exp-neg-mul-exp-eq-gumbel-cdf.md).
