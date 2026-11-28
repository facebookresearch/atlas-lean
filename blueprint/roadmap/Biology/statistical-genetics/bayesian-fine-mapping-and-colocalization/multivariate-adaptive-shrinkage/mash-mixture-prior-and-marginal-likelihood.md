# The mash mixture prior and its marginal likelihood

Let $b_{jr}$ be the true effect $j \in \{1, \dots, J\}$ in condition $r \in \{1, \dots, R\}$, observed through an estimate $\hat b_{jr}$ with standard error $\hat s_{jr}$. Write $b_j, \hat b_j \in \mathbb R^R$ for the rows. The **mash model** is

$$\hat b_j \mid b_j \sim N_R(b_j, V_j), \qquad V_j = S_j C S_j, \tag{2}$$

$$b_j \mid \pi, U \sim \sum_{k=1}^{K}\sum_{l=1}^{L} \pi_{k,l}\, N_R(0, \omega_l U_k), \tag{3}$$

where $S_j = \mathrm{diag}(\hat s_{j1}, \dots, \hat s_{jR})$, $C$ is a correlation matrix of measurement errors (for example from sample overlap between conditions), each $U_k$ is a covariance matrix describing a pattern of sharing, $\omega_1 > \dots > \omega_L > 0$ is a fixed dense grid of scales, and $\pi_{k,l} \ge 0$ with $\sum \pi_{k,l} = 1$. The source places no restriction on the $V_j$ except that each must be symmetric positive definite; with positive standard errors $\hat s_{jr} > 0$ this holds exactly when $C$ is positive definite. Since the $U_k$ are positive semidefinite, every $\omega_l U_k + V_j$ below is then positive definite, so each $N_R(\,\cdot\,; 0, \omega_l U_k + V_j)$ is a nondegenerate [multivariate Gaussian density](../../../../Probability/distributions/continuous/multivariate-normal-distribution/gaussian-density/multivariate-gaussian-pdfreal.md). Integrating out $b_j$,

$$p(\hat b_j \mid \pi, U, V_j) = \sum_{k,l} \pi_{k,l}\, N_R(\hat b_j; 0, \omega_l U_k + V_j). \tag{4}$$

Re-indexing $(k, l)$ as $p = 1, \dots, P$ with $\Sigma_p = \omega_l U_k$, the likelihood of the mixture weights under independent rows is

$$\mathcal L(\pi) = \prod_{j=1}^{J}\sum_{p=1}^{P} \pi_p\, N_R(\hat b_j; 0, \Sigma_p + V_j).$$

Its logarithm is concave in $\pi$ on the simplex, so maximizing it is a convex problem. For dependent rows it is a composite likelihood.

The covariances combine **canonical** matrices (the identity, rank-one matrices $e_r e_r^\top$ for condition-specific effects, the all-ones matrix for equal effects) with **data-driven** ones. The data-driven ones are fitted to the strongest effects by an EM algorithm for the scale-free mixture $\sum_k \pi_k N_R(0, U_k)$, initialized from principal components and sparse factors of the strong $Z$-scores. Each $U_k$ is rescaled so its largest diagonal entry is $1$. The scale grid is $\omega_l = \omega_{\max}/m^{\,l-1}$ for some $m > 1$, continued until it passes $\omega_{\min}$. The correlation $C$ is estimated from null-like rows by $\hat C = |\mathcal N|^{-1}\sum_{j \in \mathcal N} z_j z_j^\top$ with $\mathcal N = \{j : \max_r |z_{jr}| < 2\}$.

## Remarks

Equation (4) is the convolution of two centered normals: if $b \sim N(0, \Sigma)$ and $\hat b \mid b \sim N(b, V)$ then $\hat b \sim N(0, \Sigma + V)$, applied term by term to the mixture. The log-likelihood $\sum_j \log(\sum_p \pi_p L_{jp})$ with $L_{jp} = N_R(\hat b_j; 0, \Sigma_p + V_j)$ is a sum of logarithms of linear functions of $\pi$, hence concave. EM updates $\pi_p \leftarrow J^{-1}\sum_j \pi_p L_{jp}/\sum_{p'} \pi_{p'} L_{jp'}$, which can be accelerated. The scale grid lets one sharing pattern $U_k$ serve effects of very different magnitudes. In the EM fit of the data-driven $U_k$ each update keeps the rank of the matrix it started from, so initializing at low rank gives regularized low-rank patterns.

## Depends on

- [Multivariate Gaussian density function](../../../../Probability/distributions/continuous/multivariate-normal-distribution/gaussian-density/multivariate-gaussian-pdfreal.md)

## Sources

- S. M. Urbut, G. Wang, P. Carbonetto and M. Stephens, "Flexible statistical methods for estimating and testing effects in genomic studies with multiple conditions", Nature Genetics 51 (2019), 187–195 (online 2018), Online Methods ("Model and fitting", Equations (2)–(5); "Generate data-driven covariance matrices", "Generate canonical covariance matrices", "Standardize the covariance matrices", "Define grid of scaling factors", "Estimate π by maximum likelihood", "Estimating the correlation matrix C"), <https://doi.org/10.1038/s41588-018-0268-8>, PMCID PMC6309609.
