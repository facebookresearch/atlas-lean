# Effective number of independently associated SNPs

Let $M$ SNPs have causal effects $\beta_1, \dots, \beta_M$ in standardized units (phenotypic standard deviations per standard deviation of genotype), so that with no LD between causal SNPs the squared effect of a SNP is the heritability it explains and $h^2 = M\, \mathbb E[\beta^2]$, with $\beta$ the effect of a uniformly random SNP. The **effective number of independently associated SNPs** is

$$M_e = \frac{3M}{\kappa}, \qquad \kappa = \frac{\mathbb E[\beta^4]}{\mathbb E[\beta^2]^2},$$

the inverse of the kurtosis scaled so that a Gaussian (infinitesimal) architecture with independent SNPs gives $M_e = M$. Here the expectation is over a uniformly random SNP and over the randomness of its effect. In the random-effects form, where the $\beta_i$ are independent with $\beta_i \sim \mathcal N(0, \sigma_i^2)$, one has $\mathbb E[\beta^4] = 3\, \mathbb E[\sigma^4]$, so

$$M_e = \frac{\left(\sum_i \sigma_i^2\right)^2}{\sum_i \sigma_i^4} = \frac{h^2}{\mathbb E_{h^2}(\sigma^2)}, \qquad \mathbb E_{h^2}(\sigma^2) = \frac{\sum_i \sigma_i^4}{\sum_i \sigma_i^2},$$

where $\mathbb E_{h^2}(\sigma^2) = h^2/M_e$, the heritability-weighted mean per-SNP heritability, is the "average unit of heritability".

With LD, let $R$ be the LD matrix and $\alpha = R\beta$ the marginal effects; then $h^2 = M\, \mathbb E(\alpha\beta)$ and

$$M_e = \frac{3M}{\kappa_e}, \qquad \kappa_e = \frac{3\,\mathbb E(\alpha^2\beta^2) - 2\,\mathbb E(\beta^4)}{\mathbb E(\alpha\beta)^2},$$

which reduces to the definition above when $R = I$.

**Random-effects model.** Properties 1–4 are stated in the random-effects model of the source: $R$ is fixed and the causal effects are normal, $\beta \sim \mathcal N(0, \Sigma)$ with $\Sigma = \operatorname{diag}(\sigma_1^2, \dots, \sigma_M^2)$ fixed, so that $h^2 = \operatorname{Tr}(\Sigma)$. The heritability-weighted average $\mathbb E_{h^2}$ picks SNP $i$ with probability $\sigma_i^2/h^2$, the average unit of heritability is $\mathbb E_{h^2}(\alpha^2) = h^{-2}\sum_i \sigma_i^2\, \mathbb E(\alpha_i^2 \mid R, \Sigma)$, and normality ($\mathbb E(\beta_i^4 \mid \Sigma) = 3\sigma_i^4$) gives $M_e = h^2/\mathbb E_{h^2}(\alpha^2)$ in this model, which is the random-effects form above when $R = I$. Properties:

1. **Unlike the count of causal SNPs $M_t$, $M_e$ is dominated by large effects.** If $m$ large-effect SNPs explain most of $h^2$, then $M_e \approx m$ however many small nonzero effects exist; for example four SNPs with $\sigma_i^2 = 1/6$ (two thirds of $h^2 = 1$) plus many tiny effects give an average unit of about $(2/3)(1/6) = 1/9$ and $M_e \approx 9$.
2. **Bound on discoverable heritability.** For any threshold $T > 0$ on the squared marginal effect (for instance $T \approx 30/N$ for genome-wide significance at sample size $N$), the fraction of heritability explained by SNPs with $\alpha^2 > T$ satisfies

$$P_{h^2}(\alpha^2 > T) \le \frac{\mathbb E_{h^2}(\alpha^2)}{T} = \frac{h^2}{M_e\, T}.$$

3. **Prediction accuracy.** Suppose in addition that $\Sigma$ is known and that the estimated marginal effects from a GWAS of sample size $N$ are normal, $\hat\alpha \sim \mathcal N(\alpha, R/N)$. Then the optimal predictor $X\,\mathbb E(\beta \mid \hat\alpha, \Sigma)$ has accuracy $\mathbb E(r^2) = \mathbb E\big(\beta^{\mathsf T}\, \mathbb E(\alpha \mid \hat\alpha, \Sigma)\big)$, which equals

$$\mathbb E(r^2) = N \operatorname{Tr}\!\big((\Sigma R)^2 (I + N\Sigma R)^{-1}\big) = \operatorname{Tr}\!\big(R\Sigma R\,(R\Sigma R + R/N)^{-1} R\Sigma\big),$$

the second form when $R$ is invertible. For every $R$, $\mathbb E(r^2) \to h^2$ as $N \to \infty$, and $\mathbb E(r^2) = N h^4/M_e + O(N^2)$, so to first order in $N$ it is approximately $N h^4/M_e$ for small $N$. When $R = I$ (no LD) it is $\sum_i \sigma_i^4/(\sigma_i^2 + 1/N) = h^2\, \mathbb E_{h^2}\!\big(\sigma^2/(\sigma^2 + 1/N)\big)$. When $\Sigma$ is not known, this value is an upper bound on prediction accuracy. The source prints this property (Equation A8, derived in Equations A30–A31) as "$E(r^2) = h^2 E_{h^2}\big(\alpha^2/(\alpha^2 + 1/N)\big)$" for an arbitrary LD matrix $R$; this page differs because that formula is exact only when $R = I$, since its derivation shrinks each marginal estimate separately while $\hat\alpha$ has the non-diagonal covariance $R/N$. For example, with $M = 2$, $R$ having off-diagonal entry $1/2$, $\Sigma = \operatorname{diag}(1/4, 1/4)$ and $N = 4$, the exact accuracy is $4/15$ while the printed formula gives $5/18$.
4. **Infinitesimal limit.** In the homogeneous infinitesimal model, where every SNP is causal with independent normal effects of a common variance ($\beta \sim \mathcal N(0, \sigma^2 I_M)$), $M_e$ equals the effective number of independent SNPs $M_{\mathrm{indep}}$ (the number of SNPs divided by the mean LD score). Normality alone is not enough: with $R = I$ and two independent normal effects with variances proportional to $1$ and $4$, the random-effects formula gives $M_e = 25/17$, while $M_{\mathrm{indep}} = 2$.

## Remarks

Property 3 follows from $r^2 = \mathbb E\big(\beta^{\mathsf T}\, \mathbb E(\alpha \mid \hat\alpha, \Sigma)\big)$ (source Equation A29) and the normal posterior mean of the whole vector, $\mathbb E(\alpha \mid \hat\alpha, \Sigma) = R\Sigma R\,(R\Sigma R + R/N)^{-1}\hat\alpha$, because $\alpha \sim \mathcal N(0, R\Sigma R)$ and $\operatorname{cov}(\hat\alpha, \beta) = R\Sigma$; the trace simplifies to $N \operatorname{Tr}\big((\Sigma R)^2 (I + N\Sigma R)^{-1}\big)$ because $\Sigma R$ commutes with $(I + N\Sigma R)^{-1}$. The large-$N$ limit is $\operatorname{Tr}(\Sigma R) = \sum_i \sigma_i^2 R_{ii} = h^2$, and the first-order term is $N \operatorname{Tr}(\Sigma R \Sigma R) = N \sum_i \sigma_i^2\, \mathbb E(\alpha_i^2 \mid \Sigma) = N h^2\, \mathbb E_{h^2}(\alpha^2) = N h^4/M_e$. The source's Equation A30 instead uses the scalar shrinkage $\mathbb E(\alpha \mid \hat\alpha, \Sigma) = \hat\alpha\, \mathbb E(\alpha^2 \mid \Sigma)/\big(1/N + \mathbb E(\alpha^2 \mid \Sigma)\big)$ SNP by SNP, which is the exact posterior mean only when $R = I$. Property 2 is Markov's inequality applied to the heritability-weighted distribution of $\alpha^2$, whose mean is $\mathbb E_{h^2}(\alpha^2) = h^2 / M_e$. Property 1 follows because the fourth moment weights SNPs by the square of the heritability they explain. Identifiability: two SNPs in perfect LD have identical $\alpha$, so $M_e$ does not depend on whether one or both are causal, whereas a count of causal SNPs does. Applying the definition to categories of SNPs (per-SNP $M_e$), O'Connor and colleagues estimated that heritability is spread about $3.9\times$ more evenly across common SNPs than across low-frequency SNPs, across 15 well-powered traits (of the 33 analysed), and argued with an evolutionary model that negative selection "flattens" the distribution of heritability, explaining extreme polygenicity.

## Depends on

- [Mean LD score](../mean-ldscore.md)

## Sources

- L. J. O'Connor, A. P. Schoech, F. Hormozdiari, S. Gazal, N. Patterson and A. L. Price, "Extreme polygenicity of complex traits is explained by negative selection", The American Journal of Human Genetics 105 (2019), 456–476, Material and Methods (Equation 1) and Appendix A ("Definitions of $M_e$", "Properties of $M_e$", Equations A3–A10, with Equations A3–A6 and A10 for the infinitesimal limit; "Equivalence of $M_e$ Definitions" and "Polygenic Prediction Accuracy", Equations A21–A31), <https://doi.org/10.1016/j.ajhg.2019.07.003> (PMC6732528).
