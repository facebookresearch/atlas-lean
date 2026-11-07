# Bivariate LD-score model

The bivariate LD-score model (Bulik-Sullivan et al. 2015b), at the level of the cross
second moments that enter `𝔼[z₁ z₂]`: a pool of `n` genotyped individuals with genotype matrix
`X`, two GWAS samples `S₁`, `S₂` of the pool (possibly overlapping), effects `β₁`, `β₂` with
`∫ β₁ k β₂ l = (ρ_g / M) [k = l]` (genetic covariance `ρ_g`), noises `ε₁`, `ε₂` with
`∫ ε₁ i ε₂ i' = ρ_e [i = i']` (residual cross-moment `ρ_e` within an individual), effects of
each trait orthogonal to the noise of the other. The structure intentionally does not impose
within-trait moments or phenotype normalization, so it does not identify `ρ_e` with phenotypic
correlation or establish that the scaled scores below are standardized z-scores.
