# The Ornstein–Uhlenbeck solution in Itô form

Let $B$ be a real Brownian motion adapted to a filtration $F$, with increments $B_t - B_s$ independent of $F_s$ for $s \le t$, and let $t \ge 0$. Let $\theta, \sigma \in \mathbb{R}$ and let $X_0$ be any real random variable. Then for every $t \ge 0$, almost
surely,

$$e^{-\theta t} X_0 + \sigma e^{-\theta t} \int_0^t e^{\theta s}\, dB_s = x(t),$$

where $x$ is the [pathwise solution](../ornstein-uhlenbeck-process/ou-path-solution.md) of the Langevin equation
driven by $u \mapsto B_{\max(u, 0)}$ and started at $X_0$, which solves
$x(t) = X_0 - \theta \int_0^t x + \sigma (B_t - B_0)$ path by path. The left side is the Itô form
$e^{-\theta t} X_0 + \sigma \int_0^t e^{-\theta(t - s)}\, dB_s$ of the solution of $dX = -\theta X\, dt + \sigma\, dB$.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 5.6.
