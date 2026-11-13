# Conditional multivariate CLT for the bootstrap mean

Fix `E`-valued data `x` (finite-dimensional real inner product space). Let `Z` be a random vector
whose projections `⟪Z, t⟫` are `N(0, v t)`; the covariance may be singular (`v t = 0` gives the
point mass at `0`). If, for every direction `t`, the plug-in variances of the projected data
`⟪x i, t⟫` converge to `v t` and the projected data satisfy the Lindeberg condition, then,
conditionally on the data, `√n (x̄*ₙ - x̄ₙ)` converges in distribution to `Z`.

Each projection is the scalar bootstrap of the projected data (`map_world`), so the scalar
conditional Lindeberg CLT `tendstoInDistribution_bootMean` applies; the Cramér–Wold device
(`TendstoInDistribution.of_inner`) assembles the directions.
