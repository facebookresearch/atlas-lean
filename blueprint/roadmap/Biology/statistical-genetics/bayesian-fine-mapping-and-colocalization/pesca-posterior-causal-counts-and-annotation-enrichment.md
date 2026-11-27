# PESCA posterior counts of population-specific and shared causal SNPs and their enrichment

In the [PESCA two-population model](pesca-two-population-causal-status-likelihood.md) with fitted causal-status parameters $f^*$ and z-scores $Z_1,Z_2$, let $b\in\{01,10,11\}$ denote a population-specific ($01$, $10$) or shared ($11$) causal configuration.

**Per-SNP posteriors.** For each SNP $i$, the empirical Bayes posterior probabilities $\Pr(C_i=b\mid Z_1,Z_2;f^*)$ use the fitted genome-wide proportions as prior probabilities; they are approximated by Gibbs sampling, since exact evaluation sums over $2^{2p}$ configurations.

**Regional counts.** For a region of $p$ SNPs and the number $q_b$ of its SNPs in configuration $b$,

$$\mathbb E[q_b\mid Z_1,Z_2;f^*]=\sum_{i=1}^p\Pr(C_i=b\mid Z_1,Z_2;f^*),$$

by linearity of expectation applied to $q_b=\sum_i\mathbf 1\{C_i=b\}$.

**Enrichment in an annotation.** For a functional annotation $k$ containing the set $\psi(k)$ of $p_k$ SNPs, the enrichment of configuration $b$ is the ratio of posterior to prior expected counts,

$$\hat\alpha_{k,b}=\frac{\mathbb E[q_{k,b}\mid Z_1,Z_2;f^*]}{\mathbb E[q_{k,b}\mid f^*]}=\frac{\sum_{i\in\psi(k)}\Pr(C_i=b\mid Z_1,Z_2;f^*)}{p_k\Pr(C_i=b)}.$$

Its standard error is estimated by a block jackknife over approximately LD-independent blocks, and $(\hat\alpha_{k,b}-1)/\mathrm{SE}(\hat\alpha_{k,b})$ is referred to a $t$ distribution with (number of blocks $-1$) degrees of freedom, using a one-sided test of the null hypothesis $\alpha_{k,b}\le1$.

**Blocks independent in both populations.** Given LD matrices $V^{(1)}$, $V^{(2)}$ of the two populations, the transethnic LD matrix takes at each entry the correlation of larger absolute value,

$$V^{\mathrm{trans}}_{ij}=\begin{cases}V^{(1)}_{ij}&|V^{(1)}_{ij}|>|V^{(2)}_{ij}|,\\ V^{(2)}_{ij}&|V^{(2)}_{ij}|>|V^{(1)}_{ij}|,\end{cases}$$

and blocks are cut where this matrix is approximately block diagonal, so that a SNP in one block is treated as independent of all SNPs in other blocks in both populations.

## Depends on

- [PESCA: two-population likelihood of GWAS z-scores given population-specific and shared causal SNPs](pesca-two-population-causal-status-likelihood.md)
- [Posterior inclusion probability](pip.md)

## Expansion

- The prior expected count in an annotation is $p_k\Pr(C_i=b)$ because the causal statuses are i.i.d. under the fitted bivariate Bernoulli law; an enrichment above $1$ means more causal SNPs of type $b$ in the annotation than the genome-wide background predicts.
- Causal-SNP enrichment differs from heritability enrichment: the former counts causal SNPs, the latter compares average per-SNP effect sizes.
- Standard errors of regional counts are not reported, because SNPs within a region are highly correlated and the jackknife does not apply there.

## Sources

- H. Shi, K. S. Burch, R. Johnson, et al., *Localizing components of shared transethnic genetic architecture of complex traits from GWAS summary data*, American Journal of Human Genetics 106 (2020), <https://doi.org/10.1016/j.ajhg.2020.04.012>, PMCID PMC7273527 (Material and Methods: per-SNP posterior probabilities, regional numbers of causal SNPs, LD blocks independent in two populations, enrichment in functional annotations).
