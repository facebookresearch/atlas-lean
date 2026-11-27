# Phenome-wide allelic association scan

Fix a biallelic variant with alleles $A$ and $a$ and a cohort of genotyped individuals. For each phenotype $c = 1,\dots,C$ (a grouping of diagnosis codes), the **cases** are individuals carrying a code of the group, and the **controls** are the individuals who are not cases and carry no code of a phenotype-specific **exclusion set** $E_c$ of related conditions; individuals in neither group are dropped for that phenotype, so no individual is both a case and a control. Counting the two alleles of each of the $R_c$ cases and $S_c$ controls gives the table

$$\begin{array}{c|cc} & A & a \\ \hline \text{cases} & n_{11} & n_{12} \\ \text{controls} & n_{21} & n_{22} \end{array}, \qquad n_{11}+n_{12} = 2R_c, \quad n_{21}+n_{22} = 2S_c, \quad T = 2(R_c + S_c).$$

The table is **nondegenerate** when all four margins $n_{11}+n_{12}$, $n_{21}+n_{22}$, $n_{11}+n_{21}$, $n_{12}+n_{22}$ are positive. The allelic odds ratio is $\widehat{\mathrm{OR}}_c = n_{11}n_{22}/(n_{12}n_{21})$ when $n_{12}n_{21} > 0$; it is $+\infty$ when $n_{12}n_{21} = 0 < n_{11}n_{22}$ and undefined when $n_{12}n_{21} = n_{11}n_{22} = 0$. On a nondegenerate table the Pearson statistic is

$$X_c^2 = \frac{T\,(n_{11}n_{22} - n_{12}n_{21})^2}{(n_{11}+n_{12})(n_{21}+n_{22})(n_{11}+n_{21})(n_{12}+n_{22})},$$

referred to $\chi^2_1$ (a Fisher exact test replaces it when cell counts are small); on a degenerate table the phenotype gets $X_c^2 = 0$ and p-value $1$. Phenotypes with fewer than a minimum number of cases are not tested, and significance is judged at the [Bonferroni level](../../../../Probability/hypothesis-testing/bonferroni-correction/bonferroni-rejections.md) $\alpha / C'$, where $C'$ is the number of tested phenotypes.

**Proposition.** Assume the null hypothesis that the genotypes are independent of the diagnosis codes.

1. Condition on the diagnosis codes of the cohort. They determine every case count, hence the tested family and $C'$. If each tested p-value $p_c$ is [valid](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md) conditionally on the codes, $\Pr(p_c \le u \mid \text{codes}) \le u$ for $u \in [0,1]$, then the conditional probability of at least one Bonferroni-significant phenotype is at most $\alpha$, whatever the dependence among phenotypes (overlapping cases and shared controls included); so is the unconditional probability.
2. Fix a phenotype $c$. Let the retained subjects be independent and identically distributed with genotype law $p^2 + Fpq$, $2pq(1-F)$, $q^2 + Fpq$ for $AA$, $Aa$, $aa$, where $p \in (0,1)$, $q = 1 - p$ and $F \in [0,1]$, so that both alleles keep a nonzero limiting frequency, and let a retained subject be a case with probability $\rho \in (0,1)$, so that $R_c$ and $S_c$ grow without bound as the number of retained subjects tends to infinity. Then the table is nondegenerate with probability tending to $1$, and $X_c^2 \Rightarrow (1+F)\chi^2_1$. Under Hardy–Weinberg proportions ($F = 0$) the test is asymptotically calibrated; for $F > 0$ the allelic test is anticonservative and a genotype-based trend test should be used.

Within-person independence of the two alleles does not suffice for part 2 without independent sampling of subjects: if every participant were entered twice, every cell count and $X_c^2$ would double.

## Depends on

- [With two colours the multivariate hypergeometric law is hypergeometric](../cochran-armitage-trend-test/mv-hypergeometric-real-fin-two.md)
- [Bonferroni rejection set](../../../../Probability/hypothesis-testing/bonferroni-correction/bonferroni-rejections.md)
- [Valid p-value](../../../../Probability/hypothesis-testing/valid-p-values-and-false-discovery-proportion/is-valid-pvalue.md)

## Proof depends on

- [The Bonferroni procedure controls the FWER](../../../../Probability/hypothesis-testing/bonferroni-correction/measure-bonferroni-familywise-error-le.md)
- [Allelic-test variance inflation under inbreeding](../cochran-armitage-trend-test/allelic-test-miscalibration-under-hardy-weinberg.md)

## Expansion

Part 1 is the union bound applied to the conditional law given the codes, on which the tested family is fixed: $\Pr(\exists c : p_c \le \alpha/C' \mid \text{codes}) \le \sum_c \Pr(p_c \le \alpha/C' \mid \text{codes}) \le \alpha$; taking expectations removes the conditioning. Without conditioning, a filter that depended on the genotypes could select phenotypes by their p-values and break the bound. Fisher's exact p-values are conditionally valid under Hardy–Weinberg proportions, the allele table then being hypergeometric given its margins; the chi-square p-values are valid only asymptotically. For part 2, writing $\bar X_1, \bar X_0$ for the mean allele counts of cases and controls and $\hat p$ for the pooled allele frequency, a nondegenerate table has $X_c^2 = (\bar X_1 - \bar X_0)^2/[2\hat p(1-\hat p)(1/R_c + 1/S_c)]$, the allelic statistic $T_A$ of the inbreeding page, whose limit is $(1+F)\chi^2_1$. The allele counts form a $2 \times 2$ table of $T$ independent allele draws only when subjects are independent and the two alleles of a person are independent; within-person correlation changes the variance of the allele count. The exclusion sets keep related diagnoses out of the controls, which otherwise dilute effects. The first scan defined 776 phenotypes from billing codes in 6,005 genotyped patients, tested phenotypes with at least 25 cases, replicated four of seven known associations of five variants, and found Bonferroni correction conservative because the phenotypes are correlated and many are rare.

## Sources

- J. C. Denny, M. D. Ritchie, M. A. Basford et al., "PheWAS: demonstrating the feasibility of a phenome-wide scan to discover gene–disease associations", Bioinformatics 26 (2010) 1205–1210, Sections 2.2–2.4 (code translation, case and control definitions, allelic test, Bonferroni output) and Section 3 (Results), <https://doi.org/10.1093/bioinformatics/btq126>, PMCID PMC2859132.
