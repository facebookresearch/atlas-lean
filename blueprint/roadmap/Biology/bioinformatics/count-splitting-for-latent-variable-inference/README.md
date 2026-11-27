# Count splitting for latent variable inference

Selective inference for single-cell RNA-seq when the same counts are used both to estimate a latent variable (clusters, pseudotime) and to test genes for association with it. Splitting each count by binomial thinning yields a training and a test matrix that are independent under a Poisson model.

- [Poisson count splitting gives independent training and test counts](poisson-count-splitting-independence.md)
- [Correlation of count-split negative binomial counts](correlation-of-count-split-negative-binomial-counts.md)

- [Empirical Bayes batch-effect adjustment](empirical-bayes-batch-effect-adjustment/README.md)
- [Surrogate variable analysis](surrogate-variable-analysis/README.md)
