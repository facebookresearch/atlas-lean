# Covariance of LD contrast statistics and region-level aggregation

**Setting.** For SNP pairs $(X,Y)$ and $(U,V)$ (additive genotype codes), let $\Delta LD_{XY}=\widehat{\operatorname{cov}}(X,Y\mid\text{case})-\widehat{\operatorname{cov}}(X,Y\mid\text{control})$ and similarly $\Delta LD_{UV}$, with standardized statistics $T_{XY}=\widehat{\Delta LD}_{XY}/\sqrt{\operatorname{Var}\widehat{\Delta LD}_{XY}}$, as in the [LD contrast test](ld-contrast-test-and-composite-linkage-disequilibrium.md). Individuals are independent.

**Theorem 1 (case–control decomposition).**

$$\operatorname{cov}(\Delta LD_{XY},\Delta LD_{UV})=\operatorname{cov}\big[\widehat{\operatorname{cov}}(X,Y\mid\text{case}),\widehat{\operatorname{cov}}(U,V\mid\text{case})\big]+\operatorname{cov}\big[\widehat{\operatorname{cov}}(X,Y\mid\text{control}),\widehat{\operatorname{cov}}(U,V\mid\text{control})\big].$$

**Theorem 2 (covariance of sample covariances).** For an i.i.d. sample of size $n$ and unbiased sample covariances,

$$\operatorname{cov}\big(\widehat{\operatorname{cov}}(X,Y),\widehat{\operatorname{cov}}(U,V)\big)=\frac{\delta_4-\delta_2}{n}+\frac{\sigma_2+\tau_2}{n(n-1)},$$

where $\delta_4=\mathbb E[(X-\mathbb EX)(Y-\mathbb EY)(U-\mathbb EU)(V-\mathbb EV)]$, $\delta_2=\operatorname{cov}(X,Y)\operatorname{cov}(U,V)$, $\sigma_2=\operatorname{cov}(X,U)\operatorname{cov}(Y,V)$ and $\tau_2=\operatorname{cov}(X,V)\operatorname{cov}(Y,U)$.

**Theorem 3 (plug-in for $\delta_4$).** With sample means $\bar X,\dots$,

$$\mathbb E\Big[\frac1n\sum_{i=1}^n(X_i-\bar X)(Y_i-\bar Y)(U_i-\bar U)(V_i-\bar V)\Big]=\Big(1-\frac4n+\frac6{n^2}-\frac3{n^3}\Big)\delta_4+\frac{(n-1)(2n-3)}{n^3}(\delta_2+\sigma_2+\tau_2)\xrightarrow[n\to\infty]{}\delta_4 .$$

**Region–region test.** Since $\operatorname{Var}T\approx1$, $\operatorname{corr}(T_{XY},T_{UV})\approx\operatorname{cov}(T_{XY},T_{UV})\approx\operatorname{cov}(\Delta LD_{XY},\Delta LD_{UV})/\sqrt{\operatorname{Var}\Delta LD_{XY}\operatorname{Var}\Delta LD_{UV}}$. For two regions with $k_1$ and $k_2$ SNPs, model the $k_1k_2$ pair statistics as $z\sim\mathrm{MVN}(0,\Sigma)$ with $\Sigma$ estimated from Theorems 1–3, set $T=\Phi^{-1}(1-\min_ip_i/2)$, and report

$$p_{\text{region}}=1-\Pr\big(|z_i|<T\ \text{for all } i\big),\qquad z\sim\mathrm{MVN}(0,\Sigma).$$

## Depends on

- [LD contrast test and composite linkage disequilibrium](ld-contrast-test-and-composite-linkage-disequilibrium.md)

## Expansion

Theorem 1 is bilinearity of covariance plus independence of the case and control samples. Theorem 2 follows by writing each sample covariance as the U-statistic $\frac{1}{2n(n-1)}\sum_{i,j}(X_i-X_j)(Y_i-Y_j)$ and classifying index quadruples by their coincidences; only quadruples sharing indices contribute, which gives the $1/n$ and $1/(n(n-1))$ terms. For $X=Y=U=V$ it reduces to the classical variance of the sample variance, $(\mu_4-\sigma^4)/n+2\sigma^4/(n(n-1))$, and Theorem 3 to the classical expectation of the fourth sample central moment. The minimum-$p$ aggregation with the exact correlation matrix avoids both the inflation of naive combination of correlated tests and the conservativeness of Bonferroni correction over $k_1k_2$ pairs.

## Sources

- Zhang S, Jiang W, Ma RC, Yu W, "Region-based interaction detection in genome-wide case-control studies" (2019), equations (6)-(18), Theorems 1, 2 and 3 and the region-based test statistic, <https://doi.org/10.1186/s12920-019-0583-7>, PMCID PMC6936067.
