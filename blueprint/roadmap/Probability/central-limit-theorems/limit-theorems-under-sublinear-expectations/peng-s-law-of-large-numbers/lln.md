# Peng's law of large numbers under a sublinear expectation

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a sublinear expectation space and let
$Y_0, Y_1, \dots \in \mathcal{H}$ be real random variables such that, for every $i$, $Y_{i+1}$
has the same distribution as $Y_i$ and $Y_{i+1}$ is independent from $(Y_0, \dots, Y_i)$. Put
$\overline{\mu} = \mathbb{E}[Y_0]$ and $\underline{\mu} = -\mathbb{E}[-Y_0]$. Then for every
Lipschitz function $\varphi : \mathbb{R} \to \mathbb{R}$,

$$\mathbb{E}\Big[\varphi\Big(\frac{Y_0 + \dots + Y_{n-1}}{n}\Big)\Big] \to \sup_{\underline{\mu} \le y \le \overline{\mu}} \varphi(y) \qquad (n \to \infty):$$

the sample mean converges in law to the maximal distribution on
$[\underline{\mu}, \overline{\mu}]$. Identical distribution and independence are meant in Peng's
sense for sublinear expectations.

## Background

- [Laws of large numbers and random series](../../../laws-of-large-numbers/README.md): the classical
  laws. Under a linear expectation, or more generally when $Y_0$ has no mean uncertainty
  ($\mathbb{E}[Y_0] = -\mathbb{E}[-Y_0]$), the limit is the point mass at the common mean: a weak
  law of large numbers.
- [Representation of a sublinear expectation as a maximum of linear expectations](../../../foundations/sublinear-expectations-and-model-uncertainty/sublinear-expectations/is-greatest.md):
  the limit $\max_{\underline{\mu} \le y \le \overline{\mu}} \varphi(y)$ is the maximum over the
  means of the models in the representing family.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010 (published by Springer, 2019), Chapter II, Theorem 3.1 with $d = 1$, in
  the form of Remark 3.2.
