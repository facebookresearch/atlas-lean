# $G^2$ conditional-independence test on genotype tables

Let $A$ and $B$ be discrete variables (a SNP with three genotypes, or disease status) observed in $N$ individuals, and let $\mathbf{C}$ be a set of discrete conditioning variables, $\mathbf{C} = \emptyset$ allowed. Write $x_{ijk}$ for the count of individuals with $A = i$, $B = j$ and $\mathbf{C}$ in configuration $k$, with marginal totals $x_{i+k}$, $x_{+jk}$, $x_{++k}$. Under $H_0: A \perp B \mid \mathbf{C}$ the expected counts are

$$E_{ijk} = \frac{x_{i+k}\,x_{+jk}}{x_{++k}},$$

and the likelihood-ratio statistic

$$G^2 = 2\sum_{i,j,k} x_{ijk}\ln\frac{x_{ijk}}{E_{ijk}}$$

(terms with $x_{ijk} = 0$ contribute $0$) is asymptotically $\chi^2$ distributed under multinomial sampling with

$$\mathrm{df} = \bigl(\mathrm{Cat}(A)-1\bigr)\bigl(\mathrm{Cat}(B)-1\bigr)\prod_{C\in\mathbf{C}}\mathrm{Cat}(C),$$

where $\mathrm{Cat}(X)$ is the number of categories of $X$; with $\mathbf{C} = \emptyset$ this is $(\mathrm{Cat}(A)-1)(\mathrm{Cat}(B)-1)$. A Markov-blanket search for disease SNPs admits a SNP when its $G^2$ with disease status given the current blanket is significant and removes it when some conditioning subset makes it non-significant.

## Depends on

- [Uniqueness of the Markov blanket of disease status](uniqueness-of-the-markov-blanket-of-disease-status.md)
- [Multinomial distribution](../../../../../Probability/distributions/discrete/multinomial-distribution/multinomial.md)

## Proof depends on

- [Wilks' theorem, supremum form](../../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-two-mul-i-sup-lo.md)

## Expansion

Conditional independence within stratum $k$ is the hypothesis that the $A\times B$ table is a product of its margins; the maximum-likelihood fitted values are $x_{i+k}x_{+jk}/x_{++k}$, and $G^2$ is twice the log-likelihood ratio of the saturated and fitted models. Wilks' theorem gives the $\chi^2$ limit, and the degrees of freedom add over strata, each contributing $(\mathrm{Cat}(A)-1)(\mathrm{Cat}(B)-1)$. Additivity of $G^2$ over strata is the reason it is preferred to Pearson's $X^2$ for conditional tests.

## Sources

- B. Han, M. Park and X.-W. Chen, "A Markov blanket-based method for detecting causal SNPs in GWAS", BMC Bioinformatics 11 (Suppl. 3) (2010), S5, <https://doi.org/10.1186/1471-2105-11-S3-S5>, PMCID PMC2863064. Section "G2 Test", Eqs. (4) to (6).
