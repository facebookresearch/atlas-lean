# Covariance of SFS entries under Kingman's coalescent

**Covariance of SFS entries under Kingman's coalescent** (Fu 1995): with the genealogy
(holding times `K.T` and an independent random-joining block-size history `τ`) and the
conditionally Poisson counts of `SFSCondMoments`,
`Cov(ξ_i, ξ_j) = δ_{ij} θ / i + (θ / 2)² Cov(L_i, L_j)` for `1 ≤ i ≤ n - 1`, where
`L_i = sfsLength n i τ T` and the diagonal term is Fu's expected spectrum
(`SiteFrequencySpectrum.integral_sfs`). Fu's `σ_{ij}` is `Cov(L_i, L_j) / 4`.
