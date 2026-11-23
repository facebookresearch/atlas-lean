# Expected product-Bernoulli log-likelihood splits over marks

For real weights $c$ on $\{0, 1\}^d$ and $p$ with $0 < p_j < 1$ for every $j$,

$$\sum_{o} c(o) \log B_p(o) = \sum_{j=1}^{d} \bigl(n_1(c, j) \log p_j + n_0(c, j) \log(1 - p_j)\bigr),$$

where $B_p$ is the product of Bernoulli distributions (see [the normalisation](sum-bern-pmf.md)) and $n_1, n_0$ are the weights with [mark present](ones-count.md) and [absent](zeros-count.md).
