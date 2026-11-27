# Bayesian partition models for sequence clustering

Model-based clustering of aligned DNA sequences into genetically distinct groups (as in BAPS and hierBAPS) treats the partition of the sample itself as the unknown. Each cluster has its own site-wise allele frequencies with conjugate Dirichlet priors, which integrate out analytically, and a prior on partitions penalizes extra clusters; the posterior mode over partitions is then found by stochastic search, optionally re-clustering each cluster hierarchically.

- [Uniform-on-k partition prior and Dirichlet–multinomial clustering likelihood](uniform-on-k-partition-prior-and-dirichlet-multinomial-clustering-likelihood.md)
