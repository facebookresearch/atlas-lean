# Kendall's tau bridge function for the truncated Gaussian copula

**Gaussian copula model.** A random vector $x = (x_1, \dots, x_p)^\top$ follows the Gaussian copula (nonparanormal) model $x \sim \mathrm{NPN}(0, \Sigma, f)$ if there are strictly increasing functions $f_1, \dots, f_p$ with $(f_1(x_1), \dots, f_p(x_p))^\top \sim N(0, \Sigma)$ and $\sigma_{jj} = 1$.

**Truncated Gaussian copula model.** $x$ follows the truncated Gaussian copula model if there is $u \sim \mathrm{NPN}(0, \Sigma, f)$ and positive constants $c_1, \dots, c_p$ with

$$x_j = \mathbf 1(u_j > c_j)\, u_j \qquad (j = 1, \dots, p),$$

so each coordinate is either exactly zero or positive and continuous. Write $\delta_j = f_j(c_j)$; then $P(x_j = 0) = \Phi(\delta_j)$.

**Bridge function.** For an i.i.d. sample $(x_{j1}, x_{k1}), \dots, (x_{jn}, x_{kn})$ let

$$\hat\tau_{jk} = \frac{2}{n(n-1)} \sum_{1 \le i < i' \le n} \operatorname{sign}(x_{ji} - x_{ji'})\, \operatorname{sign}(x_{ki} - x_{ki'}).$$

If $(x_j, x_k)$ follows the truncated Gaussian copula with latent correlation $\sigma_{jk}$, then $\mathbb E(\hat\tau_{jk}) = F(\sigma_{jk}; \delta_j, \delta_k)$ with

$$F(\sigma; \delta_j, \delta_k) = -2\,\Phi_4(-\delta_j, -\delta_k, 0, 0; \Sigma_{4a}) + 2\,\Phi_4(-\delta_j, -\delta_k, 0, 0; \Sigma_{4b}),$$

where $\Phi_4(\cdot\,; \Sigma_4)$ is the cdf of a centred four-dimensional normal with correlation matrix $\Sigma_4$,

$$\Sigma_{4a} = \begin{pmatrix} 1 & 0 & \tfrac{1}{\sqrt2} & -\tfrac{\sigma}{\sqrt2} \\ 0 & 1 & -\tfrac{\sigma}{\sqrt2} & \tfrac{1}{\sqrt2} \\ \tfrac{1}{\sqrt2} & -\tfrac{\sigma}{\sqrt2} & 1 & -\sigma \\ -\tfrac{\sigma}{\sqrt2} & \tfrac{1}{\sqrt2} & -\sigma & 1 \end{pmatrix}, \qquad \Sigma_{4b} = \begin{pmatrix} 1 & \sigma & \tfrac{1}{\sqrt2} & \tfrac{\sigma}{\sqrt2} \\ \sigma & 1 & \tfrac{\sigma}{\sqrt2} & \tfrac{1}{\sqrt2} \\ \tfrac{1}{\sqrt2} & \tfrac{\sigma}{\sqrt2} & 1 & \sigma \\ \tfrac{\sigma}{\sqrt2} & \tfrac{1}{\sqrt2} & \sigma & 1 \end{pmatrix}.$$

Moreover $F$ is strictly increasing in $\sigma$, so it is invertible.

**Estimator.** With $n_{0j}$ the number of exact zeros of variable $j$, the moment estimator $\hat\delta_j = \Phi^{-1}(n_{0j}/n)$ is plugged in and $\hat\sigma_{jk} = F^{-1}(\hat\tau_{jk}; \hat\delta_j, \hat\delta_k)$, computed as the unique minimiser of $\{F(\sigma) - \hat\tau_{jk}\}^2$. The element-wise matrix $\hat\Sigma$ is projected to the nearest positive semidefinite correlation matrix and passed to a sparse inverse-covariance (neighbourhood-selection or graphical-lasso) estimator to obtain partial-correlation networks.

## Expansion

Because $f_j$ is strictly increasing, $\operatorname{sign}(x_{ji} - x_{ji'}) = \operatorname{sign}\{f_j(u_{ji}) - f_j(u_{ji'})\}$ whenever both observations are non-zero, so Kendall's $\tau$ only sees the latent Gaussian ranks; pairs with one or two zeros contribute according to the truncation events $\{f_j(u_j) \le \delta_j\}$. Splitting $\mathbb E\{\operatorname{sign}(\cdot)\operatorname{sign}(\cdot)\}$ over zero and non-zero events writes each term as an orthant probability of a four-dimensional Gaussian vector built from scaled latent differences and latent levels, which yields the two four-dimensional cdfs. In the untruncated limit $\delta_j, \delta_k \to -\infty$ the bridge reduces to the classical $\mathbb E\hat\tau = \tfrac{2}{\pi}\arcsin \sigma$.

## Sources

- G. Yoon, I. Gaynanova, C. L. Müller, "Microbial Networks in SPRING - Semi-parametric Rank-Based Correlation and Partial Correlation Estimation for Quantitative Microbiome Data", Frontiers in Genetics 10:516 (2019), Section 2 (Definitions 1–2, Theorem 1, Remark 1, moment estimator of the thresholds), <https://doi.org/10.3389/fgene.2019.00516> (PMC6563871).
