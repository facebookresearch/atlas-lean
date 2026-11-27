# Fixed- and random-effect SNP heritability and the two-stage estimator

**Model.** Phenotypes $y\in\mathbb R^m$ follow the sparse linear model $y=Wu^*+e$ with $e\sim N(0,\sigma_e^2 I_m)$, where $W\in\mathbb R^{m\times n}$ ($m\ll n$) holds standardized genotypes $W_{ij}=(Z_{ij}-2p_j)/\sqrt{2p_j(1-p_j)}$ ($Z_{ij}\in\{0,1,2\}$ reference-allele counts, $p_j$ allele frequencies) and the causal set $M_0=\{j:u_j^*\ne0\}$ has size $s$.

- *Fixed-effect assumption:* rows $W_{i\cdot}$ are i.i.d. with mean $0$ and positive-definite covariance $\Sigma$, $e$ is independent of $W$, and $u^*$ is fixed. Then $\tau^2=u^{*\top}\Sigma u^*$ and $h^*_{\text{fixed}}=\tau^2/(\tau^2+\sigma_e^2)$.
- *Random-effect assumption:* $\{u_j^*:j\in M_0\}$ are i.i.d. $N(0,\sigma_u^2)$, independent of $e$, with $W$ fixed. Then $h^*_{\text{rand}}=s\sigma_u^2/(s\sigma_u^2+\sigma_e^2)$.

**Proposition 1 (equivalence).** If the nonzero effects are independent draws from a distribution with mean $0$ and variance $\sigma_u^2$, each row $W_{i\cdot}$ is independent of $u^*$, and the fixed-effect total genetic variance is averaged over effects, $\tau^2=\mathbb E_{u^*}[u^{*\top}\Sigma u^*]$, then $\tau^2=s\sigma_u^2$ and $h^*_{\text{fixed}}=h^*_{\text{rand}}$.

**Two-stage estimator.** Split the sample into halves $(y^{(1)},W^{(1)})$ and $(y^{(2)},W^{(2)})$. On the first half fit the elastic net

$$\hat u=\arg\min_u\ \frac1{2m}\|y^{(1)}-W^{(1)}u\|_2^2+\alpha\lambda\|u\|_1+\frac{1-\alpha}{2}\lambda\|u\|_2^2,$$

with $(\alpha,\lambda)$ chosen by 10-fold cross-validation (largest-sparsity $\lambda$ within one standard error of the minimum error), and let $\hat M=\{j:\hat u_j\ne0\}$, $\hat n=|\hat M|$. On the second half ($m'=m/2$ samples) estimate variance components with the selected columns only: either by REML (random effects), or by the method-of-moments estimators

$$\hat\tau^2=-\frac{\hat n d_1^2}{m'(m'+1)d_2}\|y^{(2)}\|_2^2+\frac{d_1}{m'(m'+1)d_2}\|W^{(2)\top}_{\hat M}y^{(2)}\|_2^2,$$

$$\hat\sigma_e^2=\Big(1+\frac{\hat n d_1^2}{(m'+1)d_2}\Big)\frac{\|y^{(2)}\|_2^2}{m'}-\frac{d_1}{m'(m'+1)d_2}\|W^{(2)\top}_{\hat M}y^{(2)}\|_2^2=\frac{\|y^{(2)}\|_2^2}{m'}-\hat\tau^2,$$

with $d_1=\frac1{\hat n}\operatorname{tr}(\frac1{m'}W_{\hat M}^{(2)\top}W_{\hat M}^{(2)})$ and $d_2=\frac1{\hat n}\operatorname{tr}\big[(\frac1{m'}W_{\hat M}^{(2)\top}W_{\hat M}^{(2)})^2\big]-\frac1{\hat n m'}\big[\operatorname{tr}(\frac1{m'}W_{\hat M}^{(2)\top}W_{\hat M}^{(2)})\big]^2$, (the method-of-moments estimators of Dicker for high-dimensional regression with correlated predictors), and report $\hat h=\hat\tau^2/(\hat\tau^2+\hat\sigma_e^2)$.

## Expansion

For Proposition 1, $\mathbb E_{u^*}[u^{*\top}\operatorname{Cov}(W_{i\cdot})u^*]=\mathbb E_{W}\mathbb E_{u^*}[(W_{i\cdot}u^*)^2\mid W_{i\cdot}]$ because $W_{i\cdot}$ has mean zero; independence and zero mean of the effects kill cross terms, leaving $\sigma_u^2\sum_{j\in M_0}\mathbb E W_{ij}^2=s\sigma_u^2$ since standardized genotypes have unit variance. The moment estimators solve $\mathbb E\|y\|^2/m'=\tau^2+\sigma_e^2$ and an analogous identity for $\|W^\top y\|^2$, whose expectation involves the first two spectral moments $d_1,d_2$ of the empirical covariance; they are valid when the selected model is still high-dimensional and the columns are correlated. Selection and estimation must use independent halves: re-using the selection sample makes redundant selected SNPs fit noise and inflates heritability, whereas on fresh data extra columns only add variance. Shrinking to a sparse model cuts the standard error sharply (the oracle with $\hat M=M_0$ shows the attainable gain) at the cost of a small bias from missed weak effects.

## Depends on

- [GREML and Haseman–Elston estimation of SNP heritability](../README.md)
- [GREML covariance matrix $\sigma_g^2 K + \sigma_e^2 I$](../greml-cov.md)

## Sources

- Li X, Wu D, Cui Y, Liu B, Walter H, Schumann G, Li C, Jiang T, "Reliable heritability estimation using sparse regularization in ultrahigh dimensional genome-wide association studies" (2019), model (1)-(4), Proposition 1 with proof (5)-(7), and the two-stage strategy (elastic net (8) and the method-of-moments variance estimators), <https://doi.org/10.1186/s12859-019-2792-7>, PMCID PMC6492418.
