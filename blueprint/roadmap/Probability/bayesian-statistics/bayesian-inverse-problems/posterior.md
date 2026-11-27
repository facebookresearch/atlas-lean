# Posterior measure of a potential

The posterior of a prior $\mu_0$ and a potential $\Phi$ is the measure with density

$$
\frac{d\mu}{d\mu_0}(u) = \frac{1}{Z} \exp(-\Phi(u)), \qquad Z = \int \exp(-\Phi) \, d\mu_0 ,
$$

with respect to the prior (the density is read as $0$ when $Z = 0$, so the posterior is then the zero measure). For the inverse problem $y = G(u) + \eta$ with $\eta \sim N(0, \Gamma)$ the
potential is the misfit $\Phi(u; y) = \frac12 |\Gamma^{-1/2}(y - G(u))|^2$, and Bayes' theorem
identifies this measure with the conditional law of $u$ given $y$ (Dashti and Stuart, Theorem 3.4).
It is a probability measure as soon as $\exp(-\Phi)$ is integrable and $Z > 0$
([posterior is a probability measure](is-probability-measure-posterior.md)).

## Background

- [Bayes' rule for densities](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/bayes-rule/README.md):
  the identification of the posterior kernel with prior-times-likelihood, normalised, which is
  the finite-dimensional Bayes' theorem (Dashti and Stuart, Theorem 1.1) behind this definition.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Theorem 3.4, equations (3.6) and (4.1a).
