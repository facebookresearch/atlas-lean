# Pooled Poisson rate

For counts `k₁, …, kₙ` and real size factors `s₁, …, sₙ`, the pooled Poisson rate is
`μ̂ = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)`, with the convention `x / 0 = 0`: it is `0` when `∑ᵢ sᵢ = 0`, for example
for an empty family. For positive size factors it is the maximum likelihood estimate of `μ ≥ 0` in
the Poisson model `kᵢ ~ Po(sᵢ μ)`, with fitted means `sᵢ μ̂`.

For positive size factors, `n ≥ 1` and at least one positive count, it is also the limit as `a → ∞`
of the fitted prior mean `a / b̂(a)` of the Gamma–Poisson hierarchy, where `b̂(a)` is the
[rate root](rate-root.md) ([the Poisson limit](tendsto-div-rate-root.md)).
