# Partitioned GREML with several relationship matrices

Partition the SNPs into $K$ disjoint sets (chromosomes, genomic segments, or genic and intergenic regions) and let $A_c$ be the [genetic relationship matrix](grm.md) computed from the SNPs of set $c$. The partitioned mixed linear model is

$$y = X\beta + \sum_{c=1}^{K} g_c + \varepsilon, \qquad \operatorname{var}(g_c) = A_c \sigma_c^2, \quad \operatorname{var}(\varepsilon) = I \sigma_e^2,$$

with $g_1, \dots, g_K, \varepsilon$ mutually uncorrelated, so that

$$\operatorname{var}(y) = V = \sum_{c=1}^{K} A_c \sigma_c^2 + I \sigma_e^2.$$

The variance components are estimated jointly by REML, and the proportion of phenotypic variance explained by set $c$ is $h_c^2 = \sigma_c^2 / \sigma_P^2$. In the joint fit each $h_c^2$ is conditional on the other sets; fitting one set at a time (the separate analysis, $y = X\beta + g_c + \varepsilon$) inflates $h_c^2$ when SNPs in different sets are correlated, for example through population structure.

## Depends on

- [Genetic relationship matrix](grm.md)
- [GREML covariance matrix](greml-cov.md)

## Expansion

If the total genetic value is a sum of independent per-set contributions, each with covariance proportional to its own relationship matrix, then the phenotypic covariance is the stated sum, and the single-component GREML model is the case $K = 1$. The paper uses the decomposition to regress $h_c^2$ on chromosome length and gene content.

## Sources

- J. Yang et al., *Genome partitioning of genetic variation for complex traits using common SNPs*, Nat. Genet. 43 (2011), 519–525. <https://doi.org/10.1038/ng.823> (PMCID: PMC4295936) Online Methods (partitioning by chromosome, segment, and genic and intergenic regions).
