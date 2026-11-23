# The pathwise Langevin solution driven by Brownian motion is Gaussian

Let $B$ be a real Brownian motion, $\theta \ne 0$, $\sigma \in \mathbb{R}$, and $X_0 \sim N(0, v)$ ($v \ge 0$) a random
variable independent of $B$. Let $X_t$, $t \ge 0$, be the [pathwise solution](ou-path-solution.md) of the Langevin
equation driven by the path $u \mapsto B_{\max(u, 0)}$ and started at $X_0$. Then $X$ is a Gaussian process
with $\mathbb E X_t = 0$ and

$$\operatorname{Cov}(X_s, X_t) = e^{-\theta(s + t)} \Bigl( v + \sigma^2\, \frac{e^{2\theta \min(s, t)} - 1}{2\theta} \Bigr) .$$

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, Section 5.6.
