# Effective number of independently associated SNPs

Let $M$ SNPs have causal effects $\beta_1, \dots, \beta_M$ in standardized units (phenotypic standard deviations per standard deviation of genotype), so that with no LD between causal SNPs the squared effect of a SNP is the heritability it explains and $h^2 = M\, \mathbb E[\beta^2]$, with $\beta$ the effect of a uniformly random SNP. The **effective number of independently associated SNPs** is

$$M_e = \frac{3M}{\kappa}, \qquad \kappa = \frac{\mathbb E[\beta^4]}{\mathbb E[\beta^2]^2},$$

the inverse of the kurtosis scaled so that a Gaussian (infinitesimal) architecture with independent SNPs gives $M_e = M$. Here the expectation is over a uniformly random SNP and over the randomness of its effect. In the random-effects form, where the $\beta_i$ are independent with $\beta_i \sim \mathcal N(0, \sigma_i^2)$, one has $\mathbb E[\beta^4] = 3\, \mathbb E[\sigma^4]$, so

$$M_e = \frac{\left(\sum_i \sigma_i^2\right)^2}{\sum_i \sigma_i^4} = \frac{h^2}{\mathbb E_{h^2}(\sigma^2)}, \qquad \mathbb E_{h^2}(\sigma^2) = \frac{\sum_i \sigma_i^4}{\sum_i \sigma_i^2},$$

where $\mathbb E_{h^2}(\sigma^2) = h^2/M_e$, the heritability-weighted mean per-SNP heritability, is the "average unit of heritability".

With LD, let $R$ be the LD matrix and $\alpha = R\beta$ the marginal effects; then $h^2 = M\, \mathbb E(\alpha\beta)$ and

$$M_e = \frac{3M}{\kappa_e}, \qquad \kappa_e = \frac{3\,\mathbb E(\alpha^2\beta^2) - 2\,\mathbb E(\beta^4)}{\mathbb E(\alpha\beta)^2},$$

which reduces to the definition above when $R = I$. Properties:

1. **Unlike the count of causal SNPs $M_t$, $M_e$ is dominated by large effects.** If $m$ large-effect SNPs explain most of $h^2$, then $M_e \approx m$ however many small nonzero effects exist; for example four SNPs with $\sigma_i^2 = 1/6$ (two thirds of $h^2 = 1$) plus many tiny effects give an average unit of about $(2/3)(1/6) = 1/9$ and $M_e \approx 9$.
2. **Bound on discoverable heritability.** For any threshold $T > 0$ on the squared marginal effect (for instance $T \approx 30/N$ for genome-wide significance at sample size $N$), the fraction of heritability explained by SNPs with $\alpha^2 > T$ satisfies

$$P_{h^2}(\alpha^2 > T) \le \frac{\mathbb E_{h^2}(\alpha^2)}{T} = \frac{h^2}{M_e\, T}.$$

3. **Prediction accuracy at small sample size.** The optimal polygenic predictor has $\mathbb E(r^2) = h^2\, \mathbb E_{h^2}\!\big(\alpha^2/(\alpha^2 + 1/N)\big)$, which tends to $h^2$ as $N \to \infty$ and is approximately $N h^4 / M_e$ for small $N$.
4. **Infinitesimal limit.** In the homogeneous infinitesimal model, where every SNP is causal with independent normal effects of a common variance ($\beta \sim \mathcal N(0, \sigma^2 I_M)$), $M_e$ equals the effective number of independent SNPs $M_{\mathrm{indep}}$ (the number of SNPs divided by the mean LD score). Normality alone is not enough: with $R = I$ and two independent normal effects with variances proportional to $1$ and $4$, the random-effects formula gives $M_e = 25/17$, while $M_{\mathrm{indep}} = 2$.

## Remarks

Property 2 is Markov's inequality applied to the heritability-weighted distribution of $\alpha^2$, whose mean is $\mathbb E_{h^2}(\alpha^2) = h^2 / M_e$. Property 1 follows because the fourth moment weights SNPs by the square of the heritability they explain. Identifiability: two SNPs in perfect LD have identical $\alpha$, so $M_e$ does not depend on whether one or both are causal, whereas a count of causal SNPs does. Applying the definition to categories of SNPs (per-SNP $M_e$), O'Connor and colleagues estimated that heritability is spread about $3.9\times$ more evenly across common SNPs than across low-frequency SNPs in 33 traits, and argued with an evolutionary model that negative selection "flattens" the distribution of heritability, explaining extreme polygenicity.

## Depends on

- [Mean LD score](../mean-ldscore.md)

## Sources

- L. J. O'Connor, A. P. Schoech, F. Hormozdiari, S. Gazal, N. Patterson and A. L. Price, "Extreme polygenicity of complex traits is explained by negative selection", The American Journal of Human Genetics 105 (2019), 456–476, Material and Methods (Equation 1) and Appendix A ("Definitions of $M_e$", "Properties of $M_e$", Equations A3–A10, with Equations A3–A6 and A10 for the infinitesimal limit), <https://doi.org/10.1016/j.ajhg.2019.07.003> (PMC6732528).
