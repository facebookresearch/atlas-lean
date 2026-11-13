# Infinitesimal variance of the Wright–Fisher chain with mutation

In the setting of
`integral_binomial_mutatedFreq_drift`, the scaled second moment of the frequency change is
`M · E[(k / M - x) ^ 2] = p' (1 - p') + (θ₁ (1 - x) - θ₂ x) ^ 2 / (4M)` with
`p' = mutatedFreq u₁ u₂ x = x + (θ₁ (1 - x) - θ₂ x) / (2M)`. As `M → ∞` with `θ₁, θ₂, x` fixed
this tends to `x (1 - x)`, the diffusion coefficient of `mutationGenerator` (the limit itself is
not stated here).
