# Wasserstein distance under an independent shift and a scaling

Adding an independent common shift and scaling by $\gamma$ multiplies the $p$-Wasserstein distance by at most $|\gamma|$.

Let $1 \le p < \infty$, $\gamma \in \mathbb{R}$, $S_\gamma(t) = \gamma t$, and let $\rho, \nu, \mu$ be Borel probability measures on $\mathbb{R}$. Then, with $W_p$ the [Wasserstein distance of order $p$](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md) and $*$ convolution,

$$W_p\bigl(\rho * (S_\gamma)_\# \nu, \; \rho * (S_\gamma)_\# \mu\bigr) \le |\gamma| \, W_p(\nu, \mu)$$

in $[0, \infty]$, where the right side is read as $0$ when $\gamma = 0$. In random-variable form: if $R \sim \rho$ is independent of a coupled pair $(U, V)$ with $U \sim \nu$ and $V \sim \mu$, then $W_p(\mathrm{Law}(R + \gamma U), \mathrm{Law}(R + \gamma V)) \le |\gamma| \, W_p(\nu, \mu)$. No moment condition on $\rho$ is needed.

## Depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)

## Proof depends on

- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Every coupling bounds the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md)

## Expansion

Given a coupling $\pi$ of $\nu$ and $\mu$, let $R \sim \rho$ be independent of $(U, V) \sim \pi$. Then $(R + \gamma U, R + \gamma V)$ is a coupling of the two convolutions, with cost $\mathbb{E}|\gamma (U - V)|^p = |\gamma|^p \int |s - t|^p \, d\pi$; take the infimum over $\pi$. When $\gamma = 0$ both laws equal $\rho$ and the left side is $0$. These are properties (P1) and (P2) of Bellemare, Dabney and Munos, which they state without proof. The independence must be of $R$ from the pair $(U, V)$, not only from each of $U$ and $V$. Their property (P3), a bound for products with an independent random factor, is not used in this topic.

## Sources

- M. G. Bellemare, W. Dabney and R. Munos, *A Distributional Perspective on Reinforcement Learning*, Proceedings of the 34th International Conference on Machine Learning (ICML 2017); numbers from arXiv:1707.06887v1, <https://arxiv.org/abs/1707.06887v1>: Section 3.2, properties (P1) and (P2).
