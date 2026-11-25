# Two-patch loss for distinct positive τ₁, τ₂ is below the mean loss

Take two patches of the same area `A > 0` under the same incident intensity `I₀ > 0`, with
distinct positive transmission coefficients `τ₁ ≠ τ₂`, and let `τ_eff` be their
[effective power transmission coefficient](effective-power-transmission.md). Its loss is strictly
below the average of the two patch losses:
`-10 log₁₀ τ_eff < (-10 log₁₀ τ₁ + (-10 log₁₀ τ₂)) / 2`, with `log₁₀` the base-10 logarithm.
Here `τ_eff = (τ₁ + τ₂) / 2` ([two patches](effective-power-transmission-two-patch-e.md)), so
this is the [strict bound for the mean](effective-loss-lt-db-average.md): averaging decibels
overstates the effective loss.
