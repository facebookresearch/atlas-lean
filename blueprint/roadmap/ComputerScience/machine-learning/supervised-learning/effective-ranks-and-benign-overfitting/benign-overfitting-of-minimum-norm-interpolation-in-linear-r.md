# Benign overfitting of minimum-norm interpolation in linear regression

This node collects the benign-overfitting theorem of Bartlett, Long, Lugosi and Tsigler for the minimum-norm
interpolant in linear regression.

## Expansion

A sound expansion has separate pages for:

1. **Model.** A separable Hilbert space $H$, a mean-zero covariate $x \in H$ with covariance $\Sigma$ and
   $x = V\Lambda^{1/2} z$ for the spectral decomposition $\Sigma = V \Lambda V^{\mathsf T}$, where $z$ has independent
   $\sigma_x^2$-sub-Gaussian components; a mean-zero response $y$ with $\theta^*$ minimizing $\mathbb{E}(y - x^{\mathsf T}\theta)^2$,
   $\mathbb{E}[(y - x^{\mathsf T}\theta^*)^2 \mid x] \ge \sigma^2$ and $y - x^{\mathsf T}\theta^*$ conditionally $\sigma_y^2$-sub-Gaussian; almost
   surely, the projection of the $n$ data points on the orthogonal complement of any eigenvector of $\Sigma$ spans an
   $n$-dimensional space. The minimum-norm interpolant is $\hat\theta = X^{\mathsf T}(XX^{\mathsf T})^{-1}y$ and $R(\hat\theta)$ is its
   excess risk.
2. **Effective ranks.** $r_k(\Sigma) = \sum_{i > k} \lambda_i / \lambda_{k+1}$ and
   $R_k(\Sigma) = (\sum_{i > k} \lambda_i)^2 / \sum_{i > k} \lambda_i^2$, and
   $k^* = \min\{k \ge 0 : r_k(\Sigma) \ge b n\}$ (with $\min \emptyset = \infty$), defined when $\sum_i \lambda_i < \infty$.
3. **Bounds** (Theorem 4 of the source). For every $\sigma_x$ there are $b, c, c_1 > 1$ such that, for $\delta < 1$ with
   $\log(1/\delta) < n/c$: if $k^* \ge n/c_1$ then $\mathbb{E}R(\hat\theta) \ge \sigma^2/c$; otherwise, with probability at least
   $1 - \delta$,
   $R(\hat\theta) \le c\lVert\theta^*\rVert^2\lVert\Sigma\rVert \max\{\sqrt{r_0(\Sigma)/n},\ r_0(\Sigma)/n,\ \sqrt{\log(1/\delta)/n}\} + c\log(1/\delta)\sigma_y^2 (k^*/n + n/R_{k^*}(\Sigma))$,
   and $\mathbb{E}R(\hat\theta) \ge \frac{\sigma^2}{c}(k^*/n + n/R_{k^*}(\Sigma))$. Moreover, there are universal $a_1, a_2, n_0$ such that
   for all $n \ge n_0$, all $\Sigma$ and all $t \ge 0$ some $\theta^*$ with $\lVert\theta^*\rVert = t$, Gaussian $x \sim N(0, \Sigma)$ and
   $y \mid x \sim N(x^{\mathsf T}\theta^*, \lVert\theta^*\rVert^2\lVert\Sigma\rVert)$ give, with probability at least $1/4$,
   $R(\hat\theta) \ge \frac{1}{a_1}\lVert\theta^*\rVert^2\lVert\Sigma\rVert\, \mathbf{1}[r_0(\Sigma)/(n\log(1 + r_0(\Sigma))) \ge a_2]$.
4. **Benign sequences.** For covariances $\Sigma_n$ indexed by the sample size, the excess risk of the minimum-norm
   interpolant tends to zero if $r_0(\Sigma_n)/n$, $k_n^*/n$ and $n/R_{k_n^*}(\Sigma_n)$ tend to $0$, and only if
   $r_0(\Sigma_n)/(n\log(1 + r_0(\Sigma_n)))$, $k_n^*/n$ and $n/R_{k_n^*}(\Sigma_n)$ tend to $0$; the necessity of the first
   condition is in this weaker logarithmic form and comes from the worst-case $\theta^*$ of item 3.

## Related topics

- [$r_k$ is at least one](one-le-eff-rank.md)

## Sources

- Benign Overfitting in Linear Regression (Bartlett, Long, Lugosi, Tsigler, PNAS 2020; arXiv:1906.11300) — arXiv / PNAS: Definition 1 (the model), Definitions 2–3, Theorem 4 and the discussion after it defining benign sequences. <https://arxiv.org/abs/1906.11300>
