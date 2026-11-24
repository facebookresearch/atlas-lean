# Hitting probabilities equal scale ratios when both endpoints are accessible

Let $X$ be a continuous $[0, 1]$-valued solution of the martingale problem for $L = b\, \frac{d}{dx} + \frac{a}{2} \frac{d^2}{dx^2}$, with $a > 0$ and $b$ continuous on $(0, 1)$, whose scale function $S$, with [scale density](scale-density.md) and $S(0) = 0$, is finite at both endpoints. Suppose both endpoints are accessible: with speed measure $m(dy) = 2\, dy/(a(y) S'(y))$ and some $c \in (0, 1)$, $\Sigma(0) = \int_0^c S(y)\, m(dy) < \infty$ and $\Sigma(1) = \int_c^1 (S(1) - S(y))\, m(dy) < \infty$. Then, with $\tau$ the hitting time of $\{0, 1\}$,

$$\mathbb{P}_x(X_\tau = 1) = \frac{S(x)}{S(1)}, \qquad x \in (0, 1).$$

This is the special case $[l, r] = [0, 1]$ of [the scale function and exit probabilities](scale-function-and-exit-probabilities-for-one-di.md), whose hypothesis $\mathbb{P}_x(\tau < \infty) = 1$ is supplied by [the accessibility lemma](finite-accessibility-integrals-at-both-endpoints.md).

## Depends on

- [Scale function and exit probabilities for one-dimensional diffusions (process level)](scale-function-and-exit-probabilities-for-one-di.md)
- [Accessible endpoints give almost sure exit with finite mean exit time](finite-accessibility-integrals-at-both-endpoints.md)
- [Scale density of a one-dimensional diffusion](scale-density.md)

## Expansion

The statement follows from the two results it cites: the accessibility lemma gives almost sure hitting, and the exit-probability theorem then gives the ratio.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981), Chapter 15 (hitting probabilities).
