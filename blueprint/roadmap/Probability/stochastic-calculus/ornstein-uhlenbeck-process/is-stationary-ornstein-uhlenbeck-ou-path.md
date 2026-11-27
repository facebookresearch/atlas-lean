# Stationary start of the pathwise Langevin solution

Let $B$ be a real Brownian motion, $\theta > 0$, $\sigma \in \mathbb{R}$, and $X_0 \sim N(0, \sigma^2/(2\theta))$ a random
variable independent of $B$. Then the [pathwise solution](ou-path-solution.md) of the Langevin equation driven by
the path $u \mapsto B_{\max(u, 0)}$ and started at $X_0$ is a [stationary Ornstein–Uhlenbeck
process](is-stationary-ornstein-uhlenbeck.md) with rate $\theta$ and noise amplitude $\sigma$.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 5.6.
