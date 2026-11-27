# Case–case allele-frequency identity and the CC-GWAS estimators

**Identity.** Let disorders $A$ and $B$ have lifetime population prevalences $K_A, K_B \in (0,1)$. At a biallelic SNP let $p$ be the population allele frequency, $p_{A1}, p_{A0}$ the frequencies among cases and controls of $A$, and $p_{B1}, p_{B0}$ those for $B$, where controls are the population members without the disorder. Since $p = K_A p_{A1} + (1-K_A)p_{A0}$ and likewise for $B$,

$$p_{A1} - p = (1-K_A)(p_{A1} - p_{A0}), \qquad p_{A1} - p_{B1} = (1-K_A)(p_{A1}-p_{A0}) - (1-K_B)(p_{B1}-p_{B0}).$$

**Exact estimator.** With case–control effect estimates $\hat\beta_{A1A0}$ and $\hat\beta_{B1B0}$ expressed on the standardized observed scale (50/50 ascertainment), the case-versus-case effect is estimated by

$$\hat\beta^{\mathrm{Exact}}_{A1B1} = (1-K_A)\,\hat\beta_{A1A0} - (1-K_B)\,\hat\beta_{B1B0},$$

whose weights depend only on the prevalences. Its expectation is zero at any SNP whose case allele frequencies agree, including "stress-test" SNPs that affect both disorders equally in this sense, so its test controls type I error there.

**OLS estimator.** Assume the $m$ independent causal SNPs have effects on $A$ and $B$ drawn from a bivariate normal distribution with observed-scale heritabilities $h^2_{oA}, h^2_{oB}$ and coheritability $r_g h_{oA}h_{oB}$, and that the case–control estimates carry sampling errors with known variances and covariance (from the sample sizes and control overlap). The weights

$$\hat\beta^{\mathrm{OLS}}_{A1B1} = \omega_{A1A0}\,\hat\beta_{A1A0} + \omega_{B1B0}\,\hat\beta_{B1B0}$$

are the coefficients of the population regression of the true $\beta_{A1B1}$ on the two estimates, minimizing $\mathbb E[(\hat\beta_{A1B1} - \beta_{A1B1})^2]$; they satisfy $\omega_{A1A0} > 0 > \omega_{B1B0}$ and tend to the exact weights as the sample sizes grow.

**Decision rule.** A SNP is called when it reaches $P < 5\times10^{-8}$ with the OLS weights and $P < 10^{-4}$ with the exact weights; the method is intended for $r_g < 0.8$.

## Expansion

The identity is the law of total probability for the allele frequency split by disease status. The OLS weights shrink noisy case–control estimates toward the prior covariance of true effects and maximize power, but at a stress-test SNP finite-sample weights need not cancel the two disorder effects, which the exact component guards against. Because $\omega_{B1B0} < 0$, shared controls induce a positive error covariance that cancels in the difference and lowers the standard error, so control overlap increases power.

## Sources

- W. J. Peyrot, A. L. Price, "Identifying loci with different allele frequencies among cases of eight psychiatric disorders using CC-GWAS", Nature Genetics (2021), Results ("Overview of methods") and Methods ("CC-GWAS method"), <https://doi.org/10.1038/s41588-021-00787-1>.
