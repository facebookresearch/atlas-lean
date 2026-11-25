# Loss of the mean of distinct positive τ₁, τ₂ is below the mean loss

For positive `τ₁ ≠ τ₂`, the decibel loss of their arithmetic mean is strictly below the average
of their losses: `-10 log₁₀ ((τ₁ + τ₂) / 2) < (-10 log₁₀ τ₁ + (-10 log₁₀ τ₂)) / 2`, with `log₁₀`
the base-10 logarithm. Equivalently `τ₁ τ₂ < ((τ₁ + τ₂) / 2)²`, the strict inequality between
the geometric and the arithmetic mean. For two patches of equal area under a uniform incident
intensity, whose effective coefficient is the mean
([two patches](effective-power-transmission-two-patch-e.md)), averaging the decibel losses
therefore overstates the effective loss: `τ = 0.001` and `τ = 0.1` give about `12.97 dB`, not
the `20 dB` average of `30 dB` and `10 dB`.
