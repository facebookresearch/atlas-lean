# Rate Distortion

Let $\sigma^2 \ge 0$ and $D \in \mathbb{R}$. The Gaussian rate-distortion function, in bits, is

$$R(D) = \inf\left\{ I(\mu) : \mu \text{ distortion-feasible at level } D \text{ for } \sigma^2 \right\} \in [0, \infty],$$

where $I(\mu)$ is the mutual information of $\mu$ in bits (the Kullback–Leibler divergence of $\mu$ from the product of its marginals, divided by $\ln 2$). A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for the source variance $\sigma^2$ if $D \ge 0$, the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$, and $\int (x - y)^2 \, d\mu(x, y) \le D$, the integral of a nonnegative function, possibly infinite. In particular $R(D) = \infty$ for $D < 0$, the infimum of the empty set.
