# Neyman's variance estimator is conservative

For a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i}$ and $2 \le n_1 \le N - 2$, the expectation under [complete randomization](rand-exp.md) of [Neyman's variance estimator](neyman-var.md) is at least the variance of the [difference in means](diff-in-means.md),

$$\mathbb{E}_{n_1}\big[(\hat\tau - \tau)^2\big] \le \mathbb{E}_{n_1}[\hat V],$$

with equality if and only if the treatment effect $y_{1i} - y_{0i}$ is the same for all units.
