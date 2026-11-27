# Sib-pair Haseman–Elston heritability from realized genome-wide IBD

Let $n$ full-sib pairs with non-inbred parents have phenotypes $(Y_{i1}, Y_{i2})$, phenotypic variance $\sigma_P^2$, sib intraclass correlation $t$, and estimated genome-wide IBD proportions $\pi_i$, whose variance across pairs is $\operatorname{Var}(\pi)$ (about $0.0015$ for the human genome; see the [variance of genome-wide IBD sharing](variance-of-genome-wide-ibd-sharing-between-full-sibs.md)). Regress the squared differences on realized sharing,

$$(Y_{i1} - Y_{i2})^2 = \alpha + \beta\, \pi_i + e_i .$$

Ignoring dominance, $\beta = -2\sigma_A^2$, so the narrow-sense heritability estimate is

$$\hat h^2 = -\frac{\hat\beta}{2\hat\sigma_P^2}.$$

With normal phenotypes and ignoring the sampling correlation between $\hat\beta$ and $\hat\sigma_P^2$,

$$\operatorname{Var}(\hat\beta) \approx \frac{8\sigma_P^4 (1 - t)^2}{n \operatorname{Var}(\pi)}, \qquad \operatorname{Var}(\hat h^2) \approx \frac{2 (1 - t)^2}{n \operatorname{Var}(\pi)},$$

and the non-centrality parameter of the test of $h^2 = 0$ is $\lambda \approx n\, h^4 \operatorname{Var}(\pi) / (2(1-t)^2)$. With $\operatorname{Var}(\pi) = \tfrac18$ these are the single-locus QTL formulas. Detecting heritability $h^2$ from genome-wide sharing is therefore as hard as detecting a fully informative QTL explaining $q^2$ of the variance when $h^4 \operatorname{Var}(\pi) = q^4/8$, about $q^2 \approx 0.11\, h^2$ for $L = 35$ Morgans. Because the estimate uses only within-family variation in realized relatedness, it does not assume that common environment is uncorrelated with expected relatedness.

## Depends on

- [Variance of genome-wide IBD sharing between full siblings](variance-of-genome-wide-ibd-sharing-between-full-sibs.md)
- [Haseman–Elston estimator](he-estimate.md)

## Expansion

Under an additive model, $Y_{i1} - Y_{i2}$ has variance $2\sigma_P^2 - 2\operatorname{Cov}(Y_{i1}, Y_{i2} \mid \pi_i)$, with covariance $\pi_i \sigma_A^2 + \sigma_C^2$, so $\mathbb E[(Y_{i1} - Y_{i2})^2 \mid \pi_i]$ is linear in $\pi_i$ with slope $-2\sigma_A^2$. The residual variance of a squared normal difference is $2\{2\sigma_P^2(1 - t)\}^2$, and the variance of a least-squares slope is residual variance over $n \operatorname{Var}(\pi)$. Dividing by $(2\sigma_P^2)^2$ gives $\operatorname{Var}(\hat h^2)$.

## Sources

- P. M. Visscher, S. E. Medland, M. A. R. Ferreira et al., *Assumption-free estimation of heritability from genome-wide identity-by-descent sharing between full siblings*, PLoS Genet. 2 (2006), e41, <https://doi.org/10.1371/journal.pgen.0020041>, PMCID PMC1413498, Materials and Methods, "Sampling variance of estimators of genetic variance" (Haseman–Elston regression on genome-wide IBD, sampling variance and non-centrality parameter, equivalence $h^4 \operatorname{var}(\pi) = q^4/8$ and $0.11 h^2$). The displayed variance expressions are rederived above.
