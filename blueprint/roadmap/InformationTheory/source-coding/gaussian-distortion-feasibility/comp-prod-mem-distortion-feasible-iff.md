# Comp Prod mem distortion Feasible iff

Let $\sigma^2 \ge 0$, $D \ge 0$ and let $\kappa$ be a Markov kernel from $\mathbb{R}$ to $\mathbb{R}$. The joint law $\mathcal{N}(0, \sigma^2) \otimes \kappa$ is distortion-feasible at level $D$ for $\sigma^2$ if and only if

$$\int_{\mathbb{R}} \int_{\mathbb{R}} (x - y)^2 \, \kappa(x)(dy) \, \mathcal{N}(0, \sigma^2)(dx) \le D,$$

the iterated integrals being integrals of nonnegative functions with values in $[0, \infty]$. A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for the source variance $\sigma^2$ if $D \ge 0$, the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$, and $\int (x - y)^2 \, d\mu(x, y) \le D$, the integral of a nonnegative function, possibly infinite.
