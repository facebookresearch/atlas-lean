# Peng's central limit theorem under sublinear expectations

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a sublinear expectation space and let
$X_0, X_1, \dots \in \mathcal{H}$ be real random variables such that, for every $i$, $X_{i+1}$ has the
same distribution as $X_i$ and is independent from $(X_0, \dots, X_i)$, both in Peng's sense for
sublinear expectations, and such that $X_0$ has no mean uncertainty:
$\mathbb{E}[X_0] = \mathbb{E}[-X_0] = 0$. Let $\xi$ be a G-normally distributed random variable on a
sublinear expectation space $(\Omega', \mathcal{H}', \mathbb{E}')$ with the same upper and lower
variances, $\mathbb{E}'[\xi^2] = \mathbb{E}[X_0^2]$ and $\mathbb{E}'[-\xi^2] = \mathbb{E}[-X_0^2]$.
Then for every Lipschitz function $\varphi : \mathbb{R} \to \mathbb{R}$,

$$\mathbb{E}\Big[\varphi\Big(\frac{X_0 + \dots + X_{n-1}}{\sqrt{n}}\Big)\Big] \to \mathbb{E}'[\varphi(\xi)] \qquad (n \to \infty).$$

That is, the normalized sums converge in law to the G-normal distribution
$N(\{0\} \times [\underline{\sigma}^2, \overline{\sigma}^2])$, where
$\overline{\sigma}^2 = \mathbb{E}[X_0^2]$ and $\underline{\sigma}^2 = -\mathbb{E}[-X_0^2]$.

## Idea

A sublinear expectation behaves like the upper envelope of a family of ordinary expectations; it
models uncertainty about which probability law is the right one. Peng's central limit theorem says
what the classical one becomes in this setting: the normalized sum of a mean-certain sequence
converges to the G-normal distribution, characterised by the G-heat equation
$\partial_t u - G(\partial_x^2 u) = 0$ with
$G(a) = \frac12(\overline{\sigma}^2 a^+ - \underline{\sigma}^2 a^-)$. When the variance is certain
($\underline{\sigma} = \overline{\sigma}$) the G-normal law is the ordinary normal law and the classical
central limit theorem is recovered.

## Statements

- [Peng's central limit theorem under a sublinear expectation](clt.md)

## Background

- [Sublinear expectation spaces](../../../foundations/sublinear-expectations-and-model-uncertainty/sublinear-expectation-spaces/README.md):
  the setting, with distributions and independence in Peng's sense.
- [G-normal distribution](../../../foundations/sublinear-expectations-and-model-uncertainty/g-normal-distribution/README.md):
  the limit law.
- [Lindeberg–Feller central limit theorem](../../lindeberg-feller-central-limit-theorem/README.md):
  the classical theorem, the case without variance uncertainty.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546, 2010
  (published by Springer, 2019).

## Related topics

- [Sublinear expectations and model uncertainty](../../../foundations/sublinear-expectations-and-model-uncertainty/README.md):
  sublinear expectation spaces, distributions, independence and the G-normal law.
- [Laws of large numbers and random series](../../../laws-of-large-numbers/README.md): the classical
  laws of large numbers.
