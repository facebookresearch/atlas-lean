# Peng's law of large numbers under sublinear expectations

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a sublinear expectation space and let
$Y_0, Y_1, \dots \in \mathcal{H}$ be real random variables such that, for every $i$, $Y_{i+1}$ has the
same distribution as $Y_i$ and is independent from $(Y_0, \dots, Y_i)$, both in Peng's sense for
sublinear expectations. Put $\overline{\mu} = \mathbb{E}[Y_0]$ and $\underline{\mu} = -\mathbb{E}[-Y_0]$.
Then for every Lipschitz function $\varphi : \mathbb{R} \to \mathbb{R}$,

$$\mathbb{E}\Big[\varphi\Big(\frac{Y_0 + \dots + Y_{n-1}}{n}\Big)\Big] \to \sup_{\underline{\mu} \le y \le \overline{\mu}} \varphi(y) \qquad (n \to \infty):$$

the sample mean converges in law to the maximal distribution on $[\underline{\mu}, \overline{\mu}]$.

## Idea

A sublinear expectation behaves like the upper envelope of a family of ordinary expectations; it
models uncertainty about which probability law is the right one, and then the mean itself is
uncertain, between the lower mean $\underline{\mu}$ and the upper mean $\overline{\mu}$. Peng's law of
large numbers says that the sample mean does not settle on one number: it converges in law to the
maximal distribution on that interval, the law under which $\mathbb{E}[\varphi]$ is the largest value of
$\varphi$ on $[\underline{\mu}, \overline{\mu}]$. When the mean is certain, $\underline{\mu} = \overline{\mu}$,
the limit is the point mass at the mean, as in the classical weak law of large numbers.

## Statements

- [Peng's law of large numbers under a sublinear expectation](lln.md)

## Background

- [Sublinear expectation spaces](../../../foundations/sublinear-expectations-and-model-uncertainty/sublinear-expectation-spaces/README.md): the setting, with distributions and independence in Peng's sense

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546, 2010
  (published by Springer, 2019).
