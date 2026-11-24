# Empirical Bayes and Tweedie's formula

In the Gaussian location model a parameter $\mu$ is drawn from a prior $g$ and one observes $x \mid \mu \sim \mathcal N(\mu, \sigma^2)$ with $\sigma^2$ known. The Bayes rule needs the prior, but Tweedie's formula expresses the posterior mean through the marginal density $f(x) = \int \varphi_\sigma(x - \mu)\, g(d\mu)$ alone: $\mathbb E[\mu \mid x] = x + \sigma^2 (\log f)'(x)$, and similarly $\operatorname{var}[\mu \mid x] = \sigma^2 (1 + \sigma^2 (\log f)''(x))$. In empirical Bayes work many observations $x_1, \dots, x_N$ share the same prior, so $f$ can be estimated from all of them (Efron 2011, *Tweedie's formula and selection bias*). With a normal prior the formula gives linear shrinkage, and estimating the shrinkage factor from the data gives the James–Stein estimator.

Robbins' formula $\mathbb E[\theta \mid x] = (x + 1) f(x + 1)/f(x)$ is the Poisson counterpart, where $f$ is the marginal mass of the count $x$ (its probability when the prior is a probability measure). Tweedie's formulas below hold for a prior that is any finite nonzero measure (for example any probability prior, atoms allowed), and the posterior mean is identified with the conditional expectation $\mathbb E[\mu \mid x]$ when the prior has a finite first moment.

## The model

- [Marginal density of a Gaussian location mixture](gaussian-mixture-density.md)
- [Posterior mean in the Gaussian location model](gaussian-posterior-mean.md)
- [Posterior second moment in the Gaussian location model](gaussian-posterior-second-moment.md)
- [Joint law of a Gaussian location model](gaussian-location-joint.md)
- [The joint law of a Gaussian location model has the right marginal and kernel](gaussian-location-joint-prod-apply.md)

## Tweedie's formulas

- [The marginal density of a Gaussian location mixture is differentiable](has-deriv-at-gaussian-mixture-density.md)
- [The marginal density of a Gaussian location mixture is positive](gaussian-mixture-density-pos.md)
- [Tweedie's formula](gaussian-posterior-mean-eq-add-mul-deriv.md)
- [Tweedie's formula for the posterior variance](gaussian-posterior-second-moment-sub-sq.md)
- [Tweedie's formula, conditional expectation form](cond-exp-fst-gaussian-location-joint.md)

## The normal prior

- [Posterior mean in the normal–normal model](gaussian-posterior-mean-gaussian-real.md)

## Robbins' Poisson formula

- [Marginal mass of a Poisson mixture](poisson-mixture-mass.md)
- [Posterior mean in the Poisson model](poisson-posterior-mean.md)
- [Robbins' formula](poisson-posterior-mean-eq.md)

## Related topics

- [Stein's lemma and James–Stein estimation](../../statistical-estimation/stein-s-lemma-and-james-stein-estimation/README.md): the frequentist side of shrinkage; the James–Stein estimator is the normal-prior Bayes rule with its shrinkage factor estimated from the data.
- [Two-groups model and local false discovery rates](../../hypothesis-testing/two-groups-model-and-local-false-discovery-rates/README.md): Efron's other empirical Bayes model, for large-scale testing, where the local false discovery rate is a posterior probability computed from the marginal density.
- [Conjugate priors](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/conjugate-priors/README.md): the normal–normal posterior kernel, with a general prior mean.
- [Mixture models](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/mixture-models/README.md): the finite-support score identity used for Gaussian mixtures in machine learning.
