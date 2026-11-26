# Phenome-wide allelic association scan

Fix a biallelic variant with alleles $A$ and $a$ and a cohort of genotyped individuals. For each phenotype $c = 1,\dots,C$ (a grouping of diagnosis codes), the **cases** are individuals carrying a code of the group, and the **controls** are individuals carrying no code of a phenotype-specific **exclusion set** $E_c$ of related conditions; individuals in neither group are dropped for that phenotype. Counting the $2n$ alleles of each group gives the table
$$\begin{array}{c|cc} & A & a \\ \hline \text{cases} & n_{11} & n_{12} \\ \text{controls} & n_{21} & n_{22} \end{array}, \qquad T = n_{11}+n_{12}+n_{21}+n_{22},$$
with allelic odds ratio $\widehat{\mathrm{OR}}_c = n_{11}n_{22}/(n_{12}n_{21})$ and Pearson statistic
$$X_c^2 = \frac{T\,(n_{11}n_{22} - n_{12}n_{21})^2}{(n_{11}+n_{12})(n_{21}+n_{22})(n_{11}+n_{21})(n_{12}+n_{22})},$$
referred to $\chi^2_1$ (a Fisher exact test replaces it when cell counts are small). Phenotypes with fewer than a minimum number of cases are not tested, and significance is judged at the Bonferroni level $\alpha / C'$, where $C'$ is the number of tested phenotypes.

**Proposition.**

1. Under the null hypothesis that the variant is independent of every tested phenotype, the probability of at least one Bonferroni-significant phenotype is at most $\alpha$, whatever the dependence among phenotypes (overlapping cases and shared controls included), provided each per-phenotype p-value is valid.
2. If, in cases and in controls, the alleles of an individual are independent draws (Hardy–Weinberg proportions within groups), $X_c^2$ is asymptotically $\chi^2_1$ under the null; without Hardy–Weinberg proportions the allelic test is miscalibrated and a genotype-based trend test should be used.

## Depends on

- [With two colours the multivariate hypergeometric law is hypergeometric](../association-tests/cochran-armitage-trend-test/mv-hypergeometric-real-fin-two.md)
## Expansion

Part 1 is the union bound: $\Pr(\exists c : p_c \le \alpha/C') \le \sum_c \Pr(p_c \le \alpha/C') \le \alpha$. Part 2 holds because the allele counts form a $2 \times 2$ contingency table of $T$ independent allele draws only when the two alleles of a person are independent; within-person correlation changes the variance of the allele count. The exclusion sets keep related diagnoses out of the controls, which otherwise dilute effects. The first scan defined 776 phenotypes from billing codes in 6,005 genotyped patients, tested phenotypes with at least 25 cases, replicated four of seven known associations of five variants, and found Bonferroni correction conservative because the phenotypes are correlated and many are rare.

## Sources

- J. C. Denny, M. D. Ritchie, M. A. Basford et al., "PheWAS: demonstrating the feasibility of a phenome-wide scan to discover gene–disease associations", Bioinformatics 26 (2010) 1205–1210, Sections 2.2–2.4 (code translation, case and control definitions, allelic test, Bonferroni output) and Section 3 (Results), <https://doi.org/10.1093/bioinformatics/btq126>, PMCID PMC2859132.
