# Summarized-data allele score estimator

Let $G_1,\dots,G_K$ be genetic instruments for a risk factor $X$ and an outcome $Y$, measured in one sample. Let $\hat\beta_{Xk}=\operatorname{cov}(X,G_k)/\operatorname{var}(G_k)$ and $\hat\beta_{Yk}=\operatorname{cov}(Y,G_k)/\operatorname{var}(G_k)$ be the per-variant regression estimates, with standard errors $\sigma_{Xk}$ and $\sigma_{Yk}$ treated as known. For pre-specified weights $w_1,\dots,w_K$ (for example external variant–risk-factor associations), the instrumental-variable estimate based on the weighted score $Z=\sum_k w_kG_k$ is exactly

$$\frac{\operatorname{cov}(Y,Z)}{\operatorname{cov}(X,Z)}=\frac{\sum_k w_k\hat\beta_{Yk}\operatorname{var}(G_k)}{\sum_k w_k\hat\beta_{Xk}\operatorname{var}(G_k)},$$

whether or not the $G_k$ are correlated. If the instruments explain a small fraction of the outcome variance, $\operatorname{var}(G_k)$ is approximately proportional to $\sigma_{Yk}^{-2}$, which gives the summarized-data allele score estimator

$$\hat\beta_{SSw}=\frac{\sum_k w_k\hat\beta_{Yk}\sigma_{Yk}^{-2}}{\sum_k w_k\hat\beta_{Xk}\sigma_{Yk}^{-2}}.$$

For uncorrelated instruments its leading-order (first delta-method term) standard error is $\bigl(\sum_k w_k^2\sigma_{Yk}^{-2}\bigr)^{1/2}/\bigl|\sum_k w_k\hat\beta_{Xk}\sigma_{Yk}^{-2}\bigr|$.

**Equivalence with inverse-variance weighting.** With $w_k=\hat\beta_{Xk}$, the estimator $\hat\beta_{SSw}$ equals the [inverse-variance-weighted estimator](ivw.md)

$$\hat\beta_{SSt}=\frac{\sum_k\hat\beta_{Xk}\hat\beta_{Yk}\sigma_{Yk}^{-2}}{\sum_k\hat\beta_{Xk}^2\sigma_{Yk}^{-2}},$$

and the leading-order standard error above reduces to $\bigl(\sum_k\hat\beta_{Xk}^2\sigma_{Yk}^{-2}\bigr)^{-1/2}$, the usual IVW standard error. With equal weights, $\hat\beta_{SSw}$ is approximately the ratio of two inverse-variance-weighted meta-analyses, of the variant–outcome and the variant–risk-factor associations, since $\sigma_{Xk}^{-2}$ is then approximately proportional to $\sigma_{Yk}^{-2}$; the identity is exact only when $\sigma_{Xk}^{-2} \propto \sigma_{Yk}^{-2}$. The source, too, gives the proportionality as an approximation: "as the $\sigma_{Xk}^{-2}$ parameters are approximately proportional to $\sigma_{Yk}^{-2}$".

## Depends on

- [Ratio estimate of a single SNP](ratio-estimate.md)
- [Inverse-variance-weighted estimator](ivw.md)

## Expansion

Bilinearity of the sample covariance gives $\operatorname{cov}(Y,\sum_kw_kG_k)=\sum_kw_k\operatorname{cov}(Y,G_k)=\sum_kw_k\hat\beta_{Yk}\operatorname{var}(G_k)$, and likewise for $X$; no independence between variants is used. The approximation $\operatorname{var}(G_k)\propto\sigma_{Yk}^{-2}$ follows from $\sigma_{Yk}^2\approx\operatorname{var}(Y)/(n\operatorname{var}(G_k))$ when $G_k$ explains little of $\operatorname{var}(Y)$. Substituting $w_k=\hat\beta_{Xk}$ turns the numerator and denominator into those of the IVW formula. If the weights are estimated in the same data, the score reproduces two-stage least squares and inherits its weak-instrument bias, which is why the weights should be external, cross-validated, or equal.

## Sources

- S. Burgess, F. Dudbridge, S. G. Thompson, *Combining information on multiple instrumental variables in Mendelian randomization: comparison of allele score and summarized data methods*, Statistics in Medicine (2016), <https://doi.org/10.1002/sim.6835> (PMCID: PMC4832315). Section 3.2, equations (1)–(3), and Section 3.3, equations (4)–(5).
