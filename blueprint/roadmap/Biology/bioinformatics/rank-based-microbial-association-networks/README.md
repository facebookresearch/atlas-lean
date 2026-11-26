# Rank-based microbial association networks

Quantitative and relative microbiome abundance data are compositional and zero-inflated, so Pearson correlations of raw or log-transformed counts are biased. Semi-parametric rank-based estimators model each taxon as a monotone transform of a latent Gaussian variable truncated at zero, recover the latent correlation from Kendall's $\tau$ through an explicit bridge function, and feed the resulting correlation matrix to sparse inverse-covariance estimation to obtain a conditional-dependence network. A shifted log-ratio transform applied to non-zero entries only keeps zeros as the smallest values without pseudo-counts.

- [Kendall's tau bridge function for the truncated Gaussian copula](kendall-tau-bridge-for-the-truncated-gaussian-copula.md)
- [Modified centered log-ratio transform for zero-inflated compositions](modified-centered-log-ratio-transform.md)
