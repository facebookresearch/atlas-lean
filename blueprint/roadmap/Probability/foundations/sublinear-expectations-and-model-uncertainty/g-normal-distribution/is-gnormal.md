# G-normal distribution, one-dimensional

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a [sublinear expectation
space](../sublinear-expectation-spaces/sublinear-expectation-space.md). A real random variable $X \in \mathcal{H}$ is (centred)
G-normally distributed if there is $\bar{X} \in \mathcal{H}$, [identically
distributed](../sublinear-expectation-spaces/ident-distrib.md) with $X$ and [independent from](../sublinear-expectation-spaces/indep-from.md) $X$, such that
$aX + b\bar{X}$ and $\sqrt{a^2 + b^2}\, X$ are identically distributed for all $a, b \ge 0$. Its
law is determined by $\overline{\sigma}^2 = \mathbb{E}[X^2]$ and
$\underline{\sigma}^2 = -\mathbb{E}[-X^2]$ (Chapter II, Proposition 1.7 of the source for
existence; Proposition 1.10 and Corollary 1.11 for uniqueness; Remark 3.4).

## Background

- [Limit theorems under sublinear expectations](../../../central-limit-theorems/limit-theorems-under-sublinear-expectations/README.md):
  the G-normal law is the limit in Peng's central limit theorem, as the normal law is in the
  classical one; when $\mathbb{E}[X^2] = -\mathbb{E}[-X^2]$ it is the classical centred normal
  law.

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*,
  arXiv:1002.4546v1, 2010, Chapter II, Definition 1.4 with $d = 1$.
