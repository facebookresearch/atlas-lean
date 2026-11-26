# MINQUE variance components from summary statistics

Consider the partitioned linear mixed model for $n$ centred phenotypes

$$y=\sum_{i=1}^k g_i+\varepsilon,\qquad g_i\sim\mathrm{MVN}(0,\sigma_i^2K_i),\qquad \varepsilon\sim\mathrm{MVN}(0,\sigma_{k+1}^2M),$$

where $K_i=X_iX_i^{\top}/p_i$ is the genetic relatedness matrix of the $p_i$ centred SNPs (columns $x_l$, $l\in\mathcal C_i$) of category $i$, $M=I_n-\mathbf 1_n\mathbf 1_n^{\top}/n$, and the SNP heritabilities are $h_i^2=\sigma_i^2/s_y^2$ with $s_y^2=y^{\top}y/(n-1)$. **Moment identity.** For any symmetric matrices $A_1,\dots,A_k$ with $\operatorname{tr}(A_iM)=0$,

$$\mathbb E\big[y^{\top}A_iy\big]=\sum_{j=1}^k\sigma_j^2\operatorname{tr}(A_iK_j),\qquad i=1,\dots,k,$$

so the method-of-moments (MINQUE-type) estimator $\hat\sigma^2=S^{-1}q$, with $q_i=y^{\top}A_iy$ and $S_{ij}=\operatorname{tr}(A_iK_j)$, is unbiased whenever $S$ is invertible. For a general such $A_i$, $q_i$ is not a function of the marginal SNP scores: with one SNP along a centred unit vector $u$, an orthogonal centred unit vector $v$ and $A=uu^{\top}-vv^{\top}+uv^{\top}+vu^{\top}$, the phenotypes $u+v$ and $u-v$ have the same marginal score and norm but $y^{\top}Ay$ equal to $2$ and $-2$.

**Summary-statistic estimator.** Standardize SNPs so that $x_l^{\top}x_l=n$, let $\hat z_l=x_l^{\top}y/(\sqrt n\,s_y)$ be the marginal score statistic (approximately the marginal association $z$-score when each SNP explains little variance), and take prespecified SNP weights $w_l\ge0$. The weighted SNP forms with centring adjustment

$$A_i=\frac1{p_i}\sum_{l\in\mathcal C_i}w_l\,x_lx_l^{\top}-c_iM,\qquad c_i=\frac{n}{(n-1)\,p_i}\sum_{l\in\mathcal C_i}w_l,$$

satisfy $\operatorname{tr}(A_iM)=0$ (since $Mx_l=x_l$), and because $My=y$,

$$q_i=y^{\top}A_iy=\frac{n\,s_y^2}{p_i}\sum_{l\in\mathcal C_i}w_l\big(\hat z_l^2-1\big).$$

Thus $q$ needs only the marginal $z$-scores and $s_y^2$, while $S_{ij}=\operatorname{tr}(A_iK_j)$ depends only on the genotypes, through average relatedness (equivalently average weighted SNP correlation), which can be estimated from a random subset of individuals or a reference panel. The MQS framework of Zhou (2017) uses moment equations of this weighted-SNP form: equal weights reproduce Haseman–Elston cross-product regression, and weights built from LD scores and prior variance components give, for $k=1$, LD score regression with the intercept fixed at one.

## Proof sketch

For $y$ with mean zero and covariance $\Sigma=\sum_j\sigma_j^2K_j+\sigma_{k+1}^2M$, $\mathbb E[y^{\top}Ay]=\operatorname{tr}(A\Sigma)$, and the condition $\operatorname{tr}(A_iM)=0$ removes the residual variance from the equations. For the weighted forms, $y^{\top}x_lx_l^{\top}y=(x_l^{\top}y)^2=n\,s_y^2\hat z_l^2$ and $y^{\top}My=(n-1)s_y^2$, which give the displayed $q_i$. In the counterexample $u^{\top}y=1$ and $\|y\|^2=2$ for both phenotypes, $\operatorname{tr}(AM)=\operatorname{tr}(A)=0$, and $\operatorname{tr}(AK)=1\ne0$ for $K=uu^{\top}$. Solving the $k$ linear equations obtained by equating observed and expected quadratic forms is Rao's MINQUE idea; the choice of $A_i$ affects efficiency, not unbiasedness. Because $S$ averages over all SNP pairs and $q$ only over SNPs, subsampling for $S$ costs little accuracy, which makes the estimator orders of magnitude faster than REML and usable when only summary statistics are shared. Unlike REML it does not rely on normal residuals for unbiasedness.

## Depends on

- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](greml-cov.md)
- [Random-effects model of LD-score regression](../ld-score-regression/model.md)

## Sources

- X. Zhou, "A unified framework for variance component estimation with summary statistics in genome-wide association studies", Ann. Appl. Stat. 11 (2017), Section 1 and Section 2 (model (2.1), the estimator $\hat\sigma^2=S^{-1}q$ its HE and LDSC special cases, and the prespecified SNP weights shared by $q$ and $S$), <https://doi.org/10.1214/17-aoas1052>, PMCID PMC5836736.
