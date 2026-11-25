# Tradeoff function

For probability mass functions $P, Q$ on a finite type $\Omega$ and $\alpha \in \mathbb{R}$, the tradeoff function is

$$
T(P, Q)(\alpha) = \inf \{\, \beta_Q(\varphi) \mid \varphi \text{ a randomized test},\ \alpha_P(\varphi) \le \alpha \,\},
$$

the least [type-II error](beta-of.md) of a [randomized test](is-test.md) with [type-I error](alpha-of.md) at most $\alpha$, an infimum of real numbers. Outside $[0, 1]$ it is $0$: for $\alpha < 0$ the set is empty and its infimum is taken to be $0$; for $\alpha \ge 1$ the always-reject test has type-II error $0$.

## Sources

- J. Dong, A. Roth and W. J. Su, *Gaussian Differential Privacy*, Journal of the Royal Statistical Society: Series B, 2022; arXiv:1905.02383, Definition 2.1.
