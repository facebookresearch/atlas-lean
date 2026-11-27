# Compositional bias of CLR regression coefficients

Let $X_{is} > 0$ be the absolute abundance of taxon $i \in \{1, \dots, m\}$ in sample $s \in \{1, \dots, n\}$, and suppose the log absolute abundances follow the linear model

$$\log X_{is} = u_s \alpha_i + (1, c_s^\top)\beta_i + \varepsilon_{is},$$

where $u_s \in \mathbb{R}$ is the covariate of interest, $c_s \in \mathbb{R}^d$ are adjustment covariates, and $\varepsilon_{is}$ are errors. Only relative abundances are observed: read counts $Y_{is}$ with $\log\bigl(Y_{is} / \sum_k Y_{ks}\bigr) = \log\bigl(X_{is} / \sum_j X_{js}\bigr) + e_{is}$. The centered log-ratio (CLR) transform

$$W_{is} = \log \frac{Y_{is}}{\bigl(\prod_{j=1}^m Y_{js}\bigr)^{1/m}}$$

then satisfies, exactly,

$$W_{is} = u_s(\alpha_i - \bar\alpha) + (1, c_s^\top)(\beta_i - \bar\beta) + (\epsilon_{is} - \bar\epsilon_s),$$

with $\bar\alpha = m^{-1}\sum_i \alpha_i$, $\bar\beta = m^{-1}\sum_i \beta_i$, $\epsilon_{is} = \varepsilon_{is} + e_{is}$ and $\bar\epsilon_s = m^{-1}\sum_i \epsilon_{is}$. Consequently the ordinary least squares coefficient $\tilde\alpha_i$ of $u_s$ in the regression of $W_{is}$ on $z_s = (u_s, 1, c_s^\top)^\top$ is unbiased for $\alpha_i - \bar\alpha$, not for $\alpha_i$: CLR regression tests $H_{0,i}\colon \alpha_i = 0$ with bias $-\bar\alpha$, which is nonzero whenever the differential effects do not average to zero across taxa (for instance when abundant taxa change in the same direction).

## Expansion

The normalizing totals $\sum_j X_{js}$ cancel in the CLR transform because it subtracts the per-sample mean of the log proportions, which equals the mean log absolute abundance minus the same log total. Averaging the linear model over taxa gives the subtracted terms $u_s\bar\alpha + (1, c_s^\top)\bar\beta + \bar\epsilon_s$. The conditional variance of $\tilde\alpha_i$ is $\hat\rho\, n^{-1}\operatorname{var}(\epsilon_{is} - \bar\epsilon_s)$, where $\hat\rho$ is the $(1,1)$ entry of $(n^{-1}\sum_s z_s z_s^\top)^{-1}$.

## Sources

- H. Zhou, K. He, J. Chen, X. Zhang, *LinDA: linear models for differential abundance analysis of microbiome compositional data*, Genome Biology 23 (2022), 95, Methods, equations (1) to (5). <https://doi.org/10.1186/s13059-022-02655-5> (PMCID: PMC9012043)
