# Overlapping-sample bias of cross-trait polygenic-score genetic correlation

**Model.** As for the attenuation of summary-statistic genetic correlation: linear polygenic models $y_\alpha=X\alpha+\epsilon_\alpha$, $y_\eta=W\eta+\epsilon_\eta$ on $p$ independent standardized SNPs whose genotype entries are independent with mean $0$, variance $1$ and finite eighth moment (Condition 1), with $m_\alpha,m_\eta,m_{\alpha\eta}$ causal and shared causal SNPs, heritabilities $h^2_\alpha,h^2_\eta\in(0,1]$ and genetic correlation $\varphi_{\alpha\eta}=\alpha^\top\eta/(\|\alpha\|\|\eta\|)$. Now $n_s$ individuals belong both to the discovery GWAS (total size $n_1+n_s$) and to the target sample (total size $n_3+n_s$). Write $F(0,V)$ for a generic distribution with mean $0$, (co)variance $V$ and finite fourth moments. The source's assumptions on effects and errors are:

- **Condition 2 (effects and errors).** The nonzero effects are independent with $\alpha_i\sim F(0,\sigma^2_\alpha)$, $i\le m_\alpha$, and $\eta_k\sim F(0,\sigma^2_\eta)$, $k\le m_\eta$; each of the $m_{\alpha\eta}$ shared pairs satisfies $(\alpha_i,\eta_i)^\top\sim F\big(0,\begin{pmatrix}\sigma^2_\alpha&\sigma_{\alpha\eta}\\ \sigma_{\alpha\eta}&\sigma^2_\eta\end{pmatrix}\big)$ with $\sigma_{\alpha\eta}=\rho_{\alpha\eta}\sigma_\alpha\sigma_\eta$; and the random errors are independent with $\epsilon_{\alpha i}\sim F(0,\sigma^2_{\epsilon_\alpha})$ and $\epsilon_{\eta k}\sim F(0,\sigma^2_{\epsilon_\eta})$.
- **Condition 3 (errors on the shared individuals).** For each of the $n_s$ shared individuals $j$, independently over $j$, $(\epsilon_{\alpha j},\epsilon_{\eta j})^\top\sim F\big(0,\begin{pmatrix}\sigma^2_{\epsilon_\alpha}&\sigma_{\epsilon_\alpha\epsilon_\eta}\\ \sigma_{\epsilon_\alpha\epsilon_\eta}&\sigma^2_{\epsilon_\eta}\end{pmatrix}\big)$ with $\sigma_{\epsilon_\alpha\epsilon_\eta}=\rho_{\epsilon_\alpha\epsilon_\eta}\sigma_{\epsilon_\alpha}\sigma_{\epsilon_\eta}$, so the two environmental errors of a shared individual may be correlated.

Define

$$h_{\alpha\eta}=\frac{m_{\alpha\eta}\sigma_{\alpha\eta}}{m_{\alpha\eta}\sigma_{\alpha\eta}+\sigma_{\epsilon_\alpha\epsilon_\eta}}\in(0,1],$$

the share of phenotypic correlation due to genetic correlation, and let $G_{S\alpha\eta}$ be the cross-trait polygenic-score estimator (cosine between $y_\eta$ and the score built from the discovery summary statistics with all SNPs).

**Theorem.** Assume Conditions 1–3, suppose $\min(m_{\alpha\eta},m_\alpha,m_\eta)\to\infty$ as $\min\{n_1+n_s,\,n_3+n_s,\,p\}\to\infty$, and let $p=c\,\{(n_1+n_s)(n_3+n_s)\}^a$ for constants $c>0$ and $a\in(0,\infty]$. If $a\in(0,1)$, then $G_{S\alpha\eta}$ equals

$$\frac{\Big[1+\dfrac{n_sp}{(n_1+n_s)(n_3+n_s)\,h_{\alpha\eta}}\Big]\,h_\eta\,\varphi_{\alpha\eta}\,\{1+o_p(1)\}}{\Big[1+\dfrac{p}{(n_1+n_s)h^2_\alpha}+\dfrac{2n_sp}{(n_1+n_s)(n_3+n_s)}+\dfrac{n_sp^2}{(n_1+n_s)^2(n_3+n_s)\,h^2_\alpha}\Big]^{1/2}} .$$

If $a\in[1,\infty]$, then $G_{S\alpha\eta}=o_p(1)$.

In the fully overlapping case ($n_1=n_3=0$) with $h^2_\alpha=h^2_\eta=h_{\alpha\eta}=1$ this reduces to

$$G_{S\alpha\eta}=\Big(1+\frac{1}{p/n_s+n_s/p+2}\Big)^{-1/2}\varphi_{\alpha\eta}\,\{1+o_p(1)\},$$

which is biased toward zero unless $p=o(n_s)$ or $n_s=o(p)$; the bias is largest when $p$ and $n_s$ are comparable.

## Depends on

- [Asymptotic attenuation of genetic correlation estimated from GWAS summary statistics](asymptotic-attenuation-of-summary-statistic-genetic-correlation.md)

## Proof depends on

## Expansion

Shared individuals contribute their own genotype-phenotype products to both the score and the target phenotype, which inflates the numerator by the factor involving $n_s p/h_{\alpha\eta}$; non-genetic error correlation ($h_{\alpha\eta}<1$) inflates it further, which is the usual overfitting and confounding concern. At the same time the polygenic noise in the score inflates the denominator. The net effect, even in the cleanest overlapping setting, is still attenuation toward zero, so overlap does not remove the bias of summary-statistic estimators and a consistent estimator requires $h_{\alpha\eta}$ to be estimable.

## Sources

- B. Zhao, H. Zhu, "On genetic correlation estimation with summary statistics from genome-wide association studies", arXiv:1903.01301 (2019), Section "Overlapping samples", Case i): Conditions 1–3 (Conditions 1 and 2 from Section 2), Theorem 4, Remark 4, <https://doi.org/10.48550/arXiv.1903.01301>; published in *Journal of the American Statistical Association* 117(537) (2022) 1–11, <https://doi.org/10.1080/01621459.2021.1906684>. Locators follow arXiv v1.
