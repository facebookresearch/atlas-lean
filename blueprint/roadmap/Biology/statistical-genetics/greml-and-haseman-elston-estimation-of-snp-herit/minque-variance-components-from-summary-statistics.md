# MINQUE variance components from summary statistics

Consider the partitioned linear mixed model for $n$ centred phenotypes

$$y=\sum_{i=1}^k g_i+\varepsilon,\qquad g_i\sim\mathrm{MVN}(0,\sigma_i^2K_i),\qquad \varepsilon\sim\mathrm{MVN}(0,\sigma_{k+1}^2M),$$

where $K_i=X_iX_i^{\top}/p_i$ is the genetic relatedness matrix of the $p_i$ centred SNPs (columns $x_l$, $l\in\mathcal C_i$) of category $i$, $M=I_n-\mathbf 1_n\mathbf 1_n^{\top}/n$, and the SNP heritabilities are $h_i^2=\sigma_i^2/s_y^2$ with $s_y^2=y^{\top}y/(n-1)$. For any symmetric matrices $A_1,\dots,A_k$ with $\operatorname{tr}(A_iM)=0$, the moment identities

$$\mathbb E\big[y^{\top}A_iy\big]=\sum_{j=1}^k\sigma_j^2\operatorname{tr}(A_iK_j),\qquad i=1,\dots,k,$$

give the method-of-moments (MINQUE-type) estimator $\hat\sigma^2=S^{-1}q$ with $q_i=y^{\top}A_iy$ and $S_{ij}=\operatorname{tr}(A_iK_j)$, which is unbiased whenever $S$ is invertible. The phenotype enters only through quadratic forms such as

$$y^{\top}K_iy=\frac1{p_i}\sum_{l\in\mathcal C_i}\big(x_l^{\top}y\big)^2=\frac{n\,s_y^2}{p_i}\sum_{l\in\mathcal C_i}\hat z_l^2,\qquad \hat z_l=\frac{x_l^{\top}y}{\sqrt{x_l^{\top}x_l}\,s_y},$$

for SNPs standardized so that $x_l^{\top}x_l=n$, where $\hat z_l$ is the marginal score statistic (approximately the marginal association $z$-score when each SNP explains little variance). Thus $q$ needs only marginal $z$-scores, while $S$ depends only on average relatedness, equivalently average SNP correlation, which can be estimated from a random subset of individuals or a reference panel. The MQS framework of Zhou (2017) chooses SNP weights in the moment equations: equal weights reproduce Haseman–Elston cross-product regression, and weights built from LD scores and prior variance components give, for $k=1$, LD score regression with the intercept fixed at one.

## Depends on

- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](greml-cov.md)
- [Random-effects model of LD-score regression](../ld-score-regression/model.md)

## Expansion

For $y$ with mean zero and covariance $\Sigma=\sum_j\sigma_j^2K_j+\sigma_{k+1}^2M$, $\mathbb E[y^{\top}Ay]=\operatorname{tr}(A\Sigma)$, and the condition $\operatorname{tr}(A_iM)=0$ removes the residual variance from the equations. Solving the $k$ linear equations obtained by equating observed and expected quadratic forms is Rao's MINQUE idea; the choice of $A_i$ affects efficiency, not unbiasedness. Because $S$ averages over all SNP pairs and $q$ only over SNPs, subsampling for $S$ costs little accuracy, which makes the estimator orders of magnitude faster than REML and usable when only summary statistics are shared. Unlike REML it does not rely on normal residuals for unbiasedness.

## Sources

- X. Zhou, "A unified framework for variance component estimation with summary statistics in genome-wide association studies", Ann. Appl. Stat. 11 (2017), Section 1 and Section 2 (model (2.1), the estimator $\hat\sigma^2=S^{-1}q$ and its HE and LDSC special cases), <https://doi.org/10.1214/17-aoas1052>, PMCID PMC5836736.
