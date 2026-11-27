# The $\theta^2$ coefficient of Cov$(\theta_\pi,S)$ via Fu's closed form

For a natural number `n ≥ 2`, let `π_i = i (n - i) / C(n, 2)`, the weights of
[Tajima's estimator](../site-frequency-spectrum-under-variable-populatio/theta-pi.md) `θ_π = ∑_{i=1}^{n-1} π_i ξ_i` (Tajima 1983, 1989). With
[Fu's covariance matrix](fu-sigma.md) `σ` for the sample size `n`,

`∑_{i=1}^{n-1} ∑_{j=1}^{n-1} π_i σ_{ij} = (n + 2) / (2n)`.

The identity is deterministic. When the counts satisfy
`Cov(ξ_i, ξ_j) = δ_{ij} θ / i + σ_{ij} θ²` for `1 ≤ i, j ≤ n - 1` (`δ_{ij}` is `1` if `i = j`
and `0` otherwise), it is the coefficient of `θ²` in `Cov(θ_π, S)` for the number of segregating
sites `S = ∑_{i=1}^{n-1} ξ_i`. These covariances hold for a random-joining topology independent
of measurable Kingman holding times, with square-integrable counts having, given the topology
and the holding times, the first two conditional moments of independent Poisson counts with
means `(θ / 2) L_i`, where `L_i` is the
total length of the branches subtending `i` sample copies
([Fu's covariance of the site frequency spectrum](../fu-s-branch-length-covariances-for-every-sample/covariance-count-kingman-eq-fu-sigma.md)).
