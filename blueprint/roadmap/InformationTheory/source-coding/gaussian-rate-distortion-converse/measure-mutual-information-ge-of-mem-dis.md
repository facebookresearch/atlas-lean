# Measure Mutual Information ge of mem distortion Feasible

Let $0 < D < \sigma^2$ and let $\mu$ be a probability measure on $\mathbb{R}^2$ that is distortion-feasible at level $D$ for the source variance $\sigma^2$. Then its mutual information, in bits, satisfies

$$I(\mu) \ge \frac{\ln(\sigma^2 / D)}{2 \ln 2}.$$

A probability measure $\mu$ on $\mathbb{R}^2$ is distortion-feasible at level $D$ for the source variance $\sigma^2$ if $D \ge 0$, the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$, and $\int (x - y)^2 \, d\mu(x, y) \le D$, the integral of a nonnegative function, possibly infinite. The mutual information $I(\mu)$ is the Kullback–Leibler divergence of $\mu$ from the product of its marginals divided by $\ln 2$, with values in $[0, \infty]$.
