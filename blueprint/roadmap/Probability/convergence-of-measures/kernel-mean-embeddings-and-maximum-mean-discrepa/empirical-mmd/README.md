# Unbiased estimator of the squared maximum mean discrepancy

Let $X$ be a measurable space, $H$ a real reproducing kernel Hilbert space of functions on $X$ with kernel $k$, and $P$, $Q$ probability measures on $X$ for which the feature map is Bochner integrable. Let $m, n \ge 2$, let $x_1, \dots, x_m$ be independent with law $P$ and $y_1, \dots, y_n$ independent with law $Q$, the two samples independent of each other. Then the statistic

$$\mathrm{MMD}_u^2 = \frac{1}{m(m-1)} \sum_{i \ne j} k(x_i, x_j) + \frac{1}{n(n-1)} \sum_{i \ne j} k(y_i, y_j) - \frac{2}{mn} \sum_{i, j} k(x_i, y_j)$$

is an unbiased estimator of the squared maximum mean discrepancy: $\mathbb{E}[\mathrm{MMD}_u^2] = \mathrm{MMD}(P, Q)^2$.

## Idea

The population MMD is unknown; the two-sample test estimates it from data. The plug-in estimate replaces $P$ and $Q$ by the empirical measures: its square is $\|\hat\mu_P - \hat\mu_Q\|^2$, the squared distance of the empirical mean embeddings, a V-statistic. It includes the diagonal terms $k(x_i, x_i)$ and $k(y_j, y_j)$, whose expectations, when they exist (finite second moments of the norm of the feature map suffice), generally differ from that of $k(x, x')$ for independent copies, so it is generally biased. Dropping the diagonal terms and averaging each within-sample sum over its $m(m-1)$ or $n(n-1)$ ordered pairs of distinct indices, while the cross term keeps its denominator $mn$, gives the U-statistic $\mathrm{MMD}_u^2$: each remaining term pairs two independent observations, and $k$ at two independent points is integrable because the feature map is Bochner integrable under $P$ and under $Q$, so each of the three averages has the mean of $k$ at two independent points, and by linearity of expectation the mean of $\mathrm{MMD}_u^2$ is exactly $\mathbb{E}\, k(x, x') - 2\, \mathbb{E}\, k(x, y) + \mathbb{E}\, k(y, y') = \mathrm{MMD}(P, Q)^2$. The price is that $\mathrm{MMD}_u^2$ can be negative.

## Statements

- [The unbiased MMD statistic is unbiased](integral-mmd-unbiased-sq.md)
- [Unbiased empirical estimate of the squared MMD](mmd-unbiased-sq.md): definition used in the main statement
- [Two coordinates of an i.i.d. sample are independent copies](measure-preserving-pair-pi.md): lemma used in the proof of the main statement

## Background

- [Maximum mean discrepancy](../maximum-mean-discrepancy/README.md)
- [Kernel mean embedding](../kernel-mean-embedding/README.md)

## Sources

- A. Gretton, K. M. Borgwardt, M. J. Rasch, B. Schölkopf and A. Smola, *A kernel two-sample test*, Journal of Machine Learning Research (2012).
