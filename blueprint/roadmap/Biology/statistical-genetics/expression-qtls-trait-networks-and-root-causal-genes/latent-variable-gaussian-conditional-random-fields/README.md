# Latent-variable Gaussian conditional random fields

When a network among quantitative traits (such as metabolites) is inferred while conditioning on genotypes, unmeasured confounders induce spurious edges. Modeling the traits as a Gaussian conditional random field given the genotypes, and marginalizing hidden variables, splits each parameter into a sparse direct-effect part and a low-rank latent part, which a convex $\ell_1$ plus nuclear-norm penalized likelihood can separate.

- [Low-rank plus sparse Gaussian conditional random field for genotype-conditioned networks](low-rank-plus-sparse-gaussian-crf-for-genotype-conditioned-networks.md)
