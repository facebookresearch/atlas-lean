# Gaussian rate-distortion as a shared variational target

Let $\sigma^2 \ge 0$ and $D \ge 0$. A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for $\sigma^2$ if and only if its first marginal is $\mathcal{N}(0, \sigma^2)$, its square error $(x, y) \mapsto (x - y)^2$ is $\mu$-integrable and $\int (x - y)^2 \, d\mu \le D$. Consequently the Gaussian rate-distortion function, in bits, is

$$R(D) = \inf\left\{ I(\mu) : \mu_1 = \mathcal{N}(0, \sigma^2),\ (x - y)^2 \in L^1(\mu),\ \int (x - y)^2 \, d\mu \le D \right\} \in [0, \infty],$$

where $\mu_1$ is the first marginal of $\mu$ and $I(\mu)$ is its mutual information in bits. A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for the source variance $\sigma^2$ if $D \ge 0$, the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$, and $\int (x - y)^2 \, d\mu(x, y) \le D$, the integral of a nonnegative function, possibly infinite.
