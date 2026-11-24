# Non-explosivity of complex-balanced networks: further results

Besides the [non-explosivity of complex-balanced stochastic reaction networks](non-explosivity-of-complex-balanced-stochastic-reaction-networks.md), Anderson, Cappelletti, Koyama and Kurtz (2018) prove a general criterion. Let $(X_t)$ be a process on a countable state space $E \subset \mathbb{Z}^d$ with transition rates $q(x, y)$ satisfying their Condition 1 (finite rates, finite total exit rate $q(x) = \sum_{y \ne x}q(x, y)$ from each state, and bounded entrance rates into each state). If a probability distribution $\pi$ is a constant solution of the Kolmogorov forward equation ($\sum_y\pi(y)q(y, x) = \pi(x)q(x)$ for all $x$) and $\sum_x\pi(x)q(x) < \infty$, then the process is non-explosive whenever the support of the initial distribution is contained in the support of $\pi$ (their Theorem 2). The summability condition holds if and only if the embedded discrete-time chain is positive recurrent on the support of $\pi$ (their Remark 1). For a stochastic reaction system the condition reads $\sum_x\pi(x)\sum_k\lambda_k(x) < \infty$ (their Corollary 1), and the product-form Poisson distribution of a complex-balanced system satisfies it, giving non-explosivity for every initial distribution (their Theorem 3).

## Depends on

- [Non-explosivity of complex-balanced stochastic reaction networks](non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)

## Expansion

1. Condition 1 on the rates, explosion, and the minimal process.
2. Theorem 2: construction of a stationary process with marginal $\pi$ and the finiteness of the expected number of jumps per unit time.
3. Remark 1: the equivalence with positive recurrence of the embedded chain, via $\pi_Z(x) = \pi(x)q(x)$.
4. Corollary 1 for reaction networks, and Theorem 3 from the product-form distribution of Theorem 1 (Anderson, Craciun and Kurtz).

## Sources

- D. F. Anderson, D. Cappelletti, M. Koyama and T. G. Kurtz, Non-explosivity of stochastically modeled reaction networks that are complex balanced, Bull. Math. Biol. 80 (2018), 2561–2579. <https://doi.org/10.1007/s11538-018-0473-8>
