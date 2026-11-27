# Pathwise bound of stochastic mirror descent

In the setting of the [telescoped bound](mirror-descent-sum-le.md), let the prox steps use noisy vectors $G_t = g_t + \Delta_t$, where $g_t$ is a subgradient at $x_t$ of a function $f$ convex on $X$, and let all $\gamma_t > 0$. Then for every $x^\star \in X$ and $N \ge 1$ the weighted average $\tilde x_N = \big(\sum_{t<N} \gamma_t\big)^{-1}\sum_{t<N} \gamma_t x_t$ satisfies

$$
f(\tilde x_N) - f(x^\star) \le \frac{V_{x_0}(x^\star) + \frac{1}{2\alpha}\sum_{t<N} \gamma_t^2 \|G_t\|_*^2 - \sum_{t<N} \gamma_t\, \Delta_t(x_t - x^\star)}{\sum_{t<N} \gamma_t} .
$$

The inequality holds for every realization of the noise. In robust stochastic approximation $G_t = G(x_t, \xi_t)$ is an unbiased stochastic subgradient, so the noise term $\Delta_t(x_t - x^\star)$ has zero mean given $\xi_0, \ldots, \xi_{t-1}$; taking expectations gives the [efficiency estimate](integral-robust-sa-average-sub-le.md) $\mathbb{E}[f(\tilde x_N)] - f(x^\star) \le \big(D^2 + \tfrac{M_*^2}{2\alpha}\sum \gamma_t^2\big) / \sum \gamma_t$, their (2.44). Averaging is what makes the method robust: unlike classical stochastic approximation with steps $\propto 1/t$, it needs neither strong convexity nor fine tuning of the step.

## Background

- [Convergence of stochastic gradient descent](../gradient-descent/integral-sgd-average-sub-le.md): the Euclidean case in expectation, with independent stochastic subgradients.

## Sources

- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, inequality (2.39).
