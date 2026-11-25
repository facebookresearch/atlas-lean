# Loss of the mean of positive τ₁, τ₂ lies between their losses

For positive `τ₁` and `τ₂`, the decibel loss of their arithmetic mean lies between their own
losses: `-10 log₁₀ max(τ₁, τ₂) ≤ -10 log₁₀ ((τ₁ + τ₂) / 2) ≤ -10 log₁₀ min(τ₁, τ₂)`, where
`log₁₀` is the base-10 logarithm and `-10 log₁₀ τ` is the transmission loss in decibels of a
transmission coefficient `τ`. Read with `τ₁`, `τ₂` the coefficients of two patches of equal area
under a uniform incident intensity, whose effective coefficient is the mean
([two patches](effective-power-transmission-two-patch-e.md)), it says that the effective loss is
at least the smaller and at most the larger patch loss. Physical transmission coefficients satisfy
`0 < τ ≤ 1`; the inequalities need only positivity.
