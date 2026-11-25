# Value-at-risk is not subadditive

For the two independent losses `L₁` and `L₂` (each 100 with probability 0.04, else 0), the value
at risk at level `0.95` of the total loss strictly exceeds the sum of the individual values at
risk: `VaR_0.95(L₁) + VaR_0.95(L₂) = 0 + 0 < 100 = VaR_0.95(L₁ + L₂)`.
