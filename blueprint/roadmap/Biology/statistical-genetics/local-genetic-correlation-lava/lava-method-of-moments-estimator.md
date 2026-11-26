# LAVA method-of-moments estimator of the local genetic covariance

Fix a locus with $K_{\mathrm{snp}}$ standardized SNPs, genotype matrix $X$ and LD matrix $S = \operatorname{cor}(X)$. For phenotype $p$, let $Y_p = X\alpha_p + \epsilon_p$ with joint SNP effects $\alpha_p$. Prune the eigendecomposition $S = Q\Lambda^2 Q^\top$ to the $K$ leading components $Q_*, \Lambda_*$ (those explaining at least 99% of the variance), set $R = Q_*\Lambda_*^{-1}$, $W = XR$ and define the principal-component joint effects $\delta_p = \Lambda_* Q_*^\top \alpha_p \in \mathbb{R}^K$, so that $W\delta_p$ approximates the genetic component $G_p = X\alpha_p$.

For $P$ phenotypes, let $\delta = (\delta_1, \dots, \delta_P)$ be the $K \times P$ matrix of true effects and $\hat\delta$ its estimate from summary statistics, and assume

$$\hat\delta = \delta + E,$$

where the $K$ rows of $E$ are independent $N(0, \Sigma_\sigma)$, with $\Sigma_\sigma$ the known $P \times P$ sampling covariance ($\operatorname{diag}(\sigma_p^2)$ without sample overlap). Define the scaled local genetic covariance matrix $\Omega = \delta^\top\delta/K$, with entries $\omega_{pq}$.

**Statement.** $\mathbb{E}[\hat\delta^\top\hat\delta] = \delta^\top\delta + K\Sigma_\sigma = K(\Omega + \Sigma_\sigma)$, so

$$\hat\Omega = \frac{\hat\delta^\top\hat\delta}{K} - \Sigma_\sigma$$

is an unbiased estimator of $\Omega$. The local genetic correlation of phenotypes $p$ and $q$ is

$$\rho_{pq} = \frac{\omega_{pq}}{\sqrt{\omega_{pp}\,\omega_{qq}}},$$

estimated by plugging in $\hat\Omega$, and $\rho_{pq}^2$ is the proportion of local genetic variance of one phenotype explained by the other. Moreover $\hat\delta^\top\hat\delta$ has a noncentral Wishart distribution with $K$ degrees of freedom, scale matrix $\Sigma_\sigma$ and noncentrality matrix $K\Omega$, which is used to simulate null distributions for $\rho_{pq}$.

## Depends on

- [Genetic correlation in the latent causal variable model](../latent-causal-variable-model/integral-alpha1-mul-alpha2.md)

## Expansion

Expand $\hat\delta^\top\hat\delta = \delta^\top\delta + \delta^\top E + E^\top\delta + E^\top E$. The cross terms have mean zero, and $\mathbb{E}[E^\top E] = \sum_{k=1}^{K}\mathbb{E}[e_k e_k^\top] = K\Sigma_\sigma$, where $e_k^\top$ is row $k$ of $E$. Because $\delta_p^\top\delta_q = \alpha_p^\top R^{+\top}R^{+}\alpha_q \approx \alpha_p^\top S\alpha_q$, $\Omega$ is proportional to the realized covariance of the genetic components and has the same correlation structure. Sample overlap enters only through the off-diagonal entries of $\Sigma_\sigma$, which are supplied, for example, from cross-trait LD-score regression intercepts.

## Sources

- J. Werme, S. van der Sluis, D. Posthuma and C. A. de Leeuw, "An integrated framework for local genetic correlation analysis", Nature Genetics 54 (2022), 274–282, Methods, "Estimating bivariate local genetic correlations", <https://doi.org/10.1038/s41588-022-01017-y>.
