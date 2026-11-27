# K2 Bayesian score and Gini score of a k-locus genotype model

Let $L$ individuals be genotyped at biallelic SNPs coded $0, 1, 2$ and carry a phenotype with $J$ states ($J = 2$ for case–control). For a candidate set of $k$ SNPs, index the $I = 3^k$ joint genotype combinations by $i$, and let $n_{ij}$ be the number of individuals with combination $i$ and phenotype $j$, $n_i = \sum_j n_{ij}$.

**K2 score.** Model the SNPs as the parents of the phenotype node in a Bayesian network, with independent uniform Dirichlet priors on the conditional phenotype distribution for each genotype combination. The marginal likelihood of the data (Cooper–Herskovits) is

$$\mathrm{K2} = \prod_{i=1}^{I} \frac{(J-1)!}{(n_i + J - 1)!} \prod_{j=1}^{J} n_{ij}!,$$

and candidate models are ranked by $\log \mathrm{K2}$ (larger is better; implementations often minimize $-\log\mathrm{K2}$).

**Gini score.** With $p_{ij} = n_{ij}/n_i$ and $P_i = n_i / L$, the weighted Gini impurity of the partition of individuals by genotype combination is

$$\mathrm{Gini} = \sum_{i=1}^{I} P_i \Big(1 - \sum_{j=1}^{J} p_{ij}^2\Big),$$

smaller values indicating genotype classes that are purer in phenotype.

**G-test.** A shortlisted combination is tested with the likelihood-ratio statistic $G = 2\sum_{i,j} O_{ij} \ln(O_{ij}/E_{ij})$ on the $I \times J$ table (terms with $O_{ij} = 0$ omitted), referred to $\chi^2$ with $(I-1)(J-1)$ degrees of freedom, reduced for empty genotype classes, at a Bonferroni level $\alpha_0 / \binom{N}{k}$ for $N$ SNPs.

## Depends on

- [Dirichlet distribution](../../../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/dirichlet-measure.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

Integrating the multinomial likelihood $\prod_j \theta_{ij}^{n_{ij}}$ against a uniform Dirichlet density $(J-1)!$ on the simplex gives $(J-1)!\prod_j n_{ij}!/(n_i + J - 1)!$ for each genotype class, and classes are independent a priori, which yields the product. The two scores favour different epistatic architectures (K2 is a Bayesian evidence that penalizes sparse classes, Gini a misclassification-type impurity), so the screening step keeps the union of the top models under each before the G-test; a heuristic search with a two-dimensional tabu table avoids re-evaluating SNP pairs.

## Sources

- S. Tuo, J. Zhang, X. Yuan, Y. Zhang and Z. Liu, "FHSA-SED: two-locus model detection for genome-wide association study with harmony search algorithm", PLoS ONE 11(3) (2016), e0150669, Methods, Eqs. (1), (2), (5)–(7), <https://doi.org/10.1371/journal.pone.0150669>, PMCID: PMC4807955.
- G. F. Cooper and E. Herskovits, "A Bayesian method for the induction of probabilistic networks from data", Machine Learning 9 (1992), 309–347, <https://doi.org/10.1007/BF00994110>.
