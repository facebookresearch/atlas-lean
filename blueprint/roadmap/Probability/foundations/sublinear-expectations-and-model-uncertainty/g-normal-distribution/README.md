# One-dimensional G-normal distribution

Let $(\Omega, \mathcal{H}, \mathbb{E})$ be a sublinear expectation space. A real random variable $X \in \mathcal{H}$ is (centred) G-normally distributed if there is $\bar{X} \in \mathcal{H}$, identically distributed with $X$ and independent from $X$, such that $aX + b\bar{X}$ and $\sqrt{a^2 + b^2} \, X$ are identically distributed for all $a, b \ge 0$.

## Idea

For a classical centred normal variable $X$ with an independent copy $\bar{X}$, the combination $aX + b\bar{X}$ has the law of $\sqrt{a^2 + b^2} \, X$. The G-normal law takes this stability property as its definition under a sublinear expectation. Its law is determined by an upper variance $\overline{\sigma}^2 = \mathbb{E}[X^2]$ and a lower variance $\underline{\sigma}^2 = -\mathbb{E}[-X^2]$; when the two agree it is the classical centred normal law. A G-normal variable has $\mathbb{E}[X] = \mathbb{E}[-X] = 0$: its uncertainty lies in the variance, not in the mean. The letter $G$ refers to the function $G(a) = \frac{1}{2}(\overline{\sigma}^2 a^+ - \underline{\sigma}^2 a^-)$ in the nonlinear heat equation $\partial_t u = G(\partial_x^2 u)$ that describes the law. The G-normal law is the limit in Peng's central limit theorem, as the normal law is in the classical one.

## Statements

- [G-normal distribution, one-dimensional](is-gnormal.md)
- [A G-normal random variable has zero upper mean](expectation-eq-zero.md): basic property: no mean uncertainty (upper mean)
- [A G-normal random variable has zero lower mean](expectation-neg-eq-zero.md): basic property: no mean uncertainty (lower mean)

## Background

- [Sublinear expectation spaces](../sublinear-expectation-spaces/README.md)

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546, 2010.
