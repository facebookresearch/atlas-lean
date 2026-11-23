# Gaussian process regression

Regression with a zero-mean Gaussian-process prior $f \sim \mathrm{GP}(0, k)$ and Gaussian noise (Rasmussen and Williams, *Gaussian Processes for Machine Learning*, 2006, Section 2.2). On finitely many inputs everything reduces to multivariate Gaussians: the posterior at test inputs is Gaussian conditioning of the joint prior, and, when $K + \sigma^2 I$ is positive definite (for instance a positive semidefinite kernel with positive noise variance), the marginal likelihood used to select hyperparameters is the Gaussian density of the targets with covariance $K + \sigma^2 I$.

## Posterior

- [Kernel matrix](kernel-matrix.md)
- [Joint prior covariance in Gaussian-process regression](joint-cov.md)
- [Test-value projection](test-part.md)
- [Training-target projection](target-part.md)
- [Regularized kernel matrices are invertible](is-unit-det-kernel-matrix-add.md)
- [The joint covariance as a kernel matrix plus noise](joint-cov-eq-add.md)
- [The joint covariance is positive semidefinite](joint-cov-pos-semidef.md)
- [Training blocks of positive semidefinite kernel matrices](kernel-matrix-pos-semidef-train.md)
- [The Gaussian-process posterior](cond-distrib-test-given-targets.md)

## Marginal likelihood

- [Regularized kernel matrices are positive definite](pos-def-kernel-matrix-add.md)
- [Marginal law of the targets in Gaussian-process regression](map-targets-eq.md)
- [Density of the targets in Gaussian-process regression](map-targets-eq-with-density.md)
- [Log marginal likelihood of Gaussian-process regression](log-marginal-likelihood.md)
- [The log marginal likelihood of Gaussian-process regression](log-marginal-likelihood-2.md)

## Related topics

- [Gaussian conditioning](../../../../Probability/distributions/continuous/gaussian-conditioning/README.md): the Schur-complement formula behind the posterior and the linear-Gaussian marginal behind the evidence.
- [Bayesian linear regression](../../bayesian-inference-and-sampling/bayesian-linear-regression/README.md): the weight-space view: a linear model with a Gaussian prior on its weights is a Gaussian process (Rasmussen and Ghahramani 2001, Section 2), and its evidence is again a Gaussian marginal density of the data.
- [Multivariate normal distribution](../../../../Probability/distributions/continuous/multivariate-normal-distribution/README.md): the density formula used for the marginal likelihood.
- [Bayesian inverse problems](../../../../Probability/bayesian-statistics/bayesian-inverse-problems/README.md): Gaussian-process regression is the linear case of a Bayesian inverse problem; for nonlinear forward maps the posterior is a reweighting of the Gaussian prior that is no longer Gaussian.
