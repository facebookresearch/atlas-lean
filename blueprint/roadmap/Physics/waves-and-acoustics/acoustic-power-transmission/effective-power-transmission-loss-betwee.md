# Two-patch loss for positive τ₁, τ₂ lies between the patch losses

Take two patches of the same area `A > 0` under the same incident intensity `I₀ > 0`, with
positive transmission coefficients `τ₁` and `τ₂`, and let `τ_eff` be their
[effective power transmission coefficient](effective-power-transmission.md). Its loss lies
between the two patch losses:
`-10 log₁₀ max(τ₁, τ₂) ≤ -10 log₁₀ τ_eff ≤ -10 log₁₀ min(τ₁, τ₂)`, with `log₁₀` the base-10
logarithm. Here `τ_eff = (τ₁ + τ₂) / 2` ([two patches](effective-power-transmission-two-patch-e.md)),
so this is the [bound for the mean](effective-loss-between.md).
