# Overlapping-sample bias of cross-trait polygenic-score genetic correlation

**Model.** As for the attenuation of summary-statistic genetic correlation: linear polygenic models $y_\alpha=X\alpha+\epsilon_\alpha$, $y_\eta=W\eta+\epsilon_\eta$ on $p$ independent standardized SNPs, with $m_\alpha,m_\eta,m_{\alpha\eta}\to\infty$ causal and shared causal SNPs, heritabilities $h^2_\alpha,h^2_\eta\in(0,1]$ and genetic correlation $\varphi_{\alpha\eta}=\alpha^\top\eta/(\|\alpha\|\|\eta\|)$. Now $n_s$ individuals belong both to the discovery GWAS (total size $n_1+n_s$) and to the target sample (total size $n_3+n_s$), and on these shared individuals the environmental errors may be correlated with covariance $\sigma_{\epsilon_\alpha\epsilon_\eta}$. Define

$$h_{\alpha\eta}=\frac{m_{\alpha\eta}\sigma_{\alpha\eta}}{m_{\alpha\eta}\sigma_{\alpha\eta}+\sigma_{\epsilon_\alpha\epsilon_\eta}}\in(0,1],$$

the share of phenotypic correlation due to genetic correlation, and let $G_{S\alpha\eta}$ be the cross-trait polygenic-score estimator (cosine between $y_\eta$ and the score built from the discovery summary statistics with all SNPs).

**Theorem.** Let $p=c\,\{(n_1+n_s)(n_3+n_s)\}^a$. If $a\in(0,1)$, then $G_{S\alpha\eta}$ equals

$$\frac{\Big[1+\dfrac{n_sp}{(n_1+n_s)(n_3+n_s)\,h_{\alpha\eta}}\Big]\,h_\eta\,\varphi_{\alpha\eta}\,\{1+o_p(1)\}}{\Big[1+\dfrac{p}{(n_1+n_s)h^2_\alpha}+\dfrac{2n_sp}{(n_1+n_s)(n_3+n_s)}+\dfrac{n_sp^2}{(n_1+n_s)^2(n_3+n_s)\,h^2_\alpha}\Big]^{1/2}} .$$

If $a\ge1$, then $G_{S\alpha\eta}=o_p(1)$.

In the fully overlapping case ($n_1=n_3=0$) with $h^2_\alpha=h^2_\eta=h_{\alpha\eta}=1$ this reduces to

$$G_{S\alpha\eta}=\Big(1+\frac{1}{p/n_s+n_s/p+2}\Big)^{-1/2}\varphi_{\alpha\eta}\,\{1+o_p(1)\},$$

which is biased toward zero unless $p=o(n_s)$ or $n_s=o(p)$; the bias is largest when $p$ and $n_s$ are comparable.

## Depends on

- [Asymptotic attenuation of genetic correlation estimated from GWAS summary statistics](asymptotic-attenuation-of-summary-statistic-genetic-correlation.md)

## Proof depends on

## Expansion

Shared individuals contribute their own genotype-phenotype products to both the score and the target phenotype, which inflates the numerator by the factor involving $n_s p/h_{\alpha\eta}$; non-genetic error correlation ($h_{\alpha\eta}<1$) inflates it further, which is the usual overfitting and confounding concern. At the same time the polygenic noise in the score inflates the denominator. The net effect, even in the cleanest overlapping setting, is still attenuation toward zero, so overlap does not remove the bias of summary-statistic estimators and a consistent estimator requires $h_{\alpha\eta}$ to be estimable.

## Sources

- B. Zhao, H. Zhu, "On genetic correlation estimation with summary statistics from genome-wide association studies", arXiv:1903.01301 (2019), Section "Overlapping samples", Case i): Condition 3, Theorem 4, Remark 4, <https://doi.org/10.48550/arXiv.1903.01301>; published in *Journal of the American Statistical Association* 117(537) (2022) 1–11, <https://doi.org/10.1080/01621459.2021.1906684>. Locators follow arXiv v1.
