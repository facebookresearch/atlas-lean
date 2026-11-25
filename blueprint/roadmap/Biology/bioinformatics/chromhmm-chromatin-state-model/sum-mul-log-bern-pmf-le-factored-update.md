# The factored update maximizes the expected log-likelihood

Let $c(o) \ge 0$ for every $o \in \{0, 1\}^d$, with $n_1(c, j) > 0$ and $n_0(c, j) > 0$ for every mark $j$. Then for every $p$ with $0 < p_j < 1$,

$$\sum_{o} c(o) \log B_p(o) \le \sum_{o} c(o) \log B_{\hat p}(o),$$

where $B$ is the product of Bernoulli distributions and $\hat p$ the [factored update](factored-update.md).
