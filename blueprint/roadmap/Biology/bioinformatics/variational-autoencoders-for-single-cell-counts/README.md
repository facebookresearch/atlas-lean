# Variational autoencoders for single-cell counts

Hierarchical Bayesian models of single-cell RNA-sequencing counts whose conditional distributions are parameterized by neural networks and fitted by amortized variational inference. The counts follow a zero-inflated negative binomial law given a low-dimensional latent state, a library-size factor and the batch, and the same fitted model serves normalization, batch correction, clustering and differential expression.

- [Zero-inflated negative binomial likelihood of the scVI generative model](zero-inflated-negative-binomial-likelihood-of-the-scvi-generative-model.md)
- [Evidence lower bound with a library-size latent variable](evidence-lower-bound-with-a-library-size-latent-variable.md)
- [Bayes factor for differential expression from a variational posterior](bayes-factor-for-differential-expression-from-a-variational-posterior.md)
