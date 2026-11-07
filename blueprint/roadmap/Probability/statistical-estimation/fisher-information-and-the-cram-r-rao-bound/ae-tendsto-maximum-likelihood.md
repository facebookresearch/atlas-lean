# Wald's consistency theorem for maximum likelihood

**Wald's consistency theorem for maximum likelihood** (Ferguson's form, positive
densities). Let `Θ` be a compact metric space and `p θ` probability densities with respect to
`ν`, positive, measurable in `x` and continuous in `θ`. Assume the model is identifiable
(`p θ = p θ₀` `ν`-a.e. only for `θ = θ₀`) and that the log-likelihood ratios have an upper
envelope `K` integrable under `p θ₀`. Let `X 0, X 1, …` be independent with law `p θ₀ ν`, and
let `θhat n ω` maximize the log-likelihood `∑_{i<n} log p θ (X i ω)` over `θ ∈ Θ`. Then
`θhat n → θ₀` almost surely.

## Sources

- Wald (1949); Ferguson (1996), Theorem 17. Proves the deferred entry `ae_tendsto_maximumLikelihood`.
