# The $\theta^2$ coefficient of Cov$(\theta_\pi,S)$ via Fu's closed form

For a natural number `n ≥ 2`, let `π_i = i (n - i) / C(n, 2)`, the weights of
[Tajima's estimator](../site-frequency-spectrum-under-variable-populatio/theta-pi.md) `θ_π = ∑_{i=1}^{n-1} π_i ξ_i` (Tajima 1983, 1989). With
[Fu's covariance matrix](fu-sigma.md) `σ` for the sample size `n`,

`∑_{i=1}^{n-1} ∑_{j=1}^{n-1} π_i σ_{ij} = (n + 2) / (2n)`.

Under Kingman's coalescent, where `Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²`, this is the
coefficient of `θ²` in `Cov(θ_π, S)` for the number of segregating sites `S = ∑_{i=1}^{n-1} ξ_i`.
