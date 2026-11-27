# Power of a local-ancestry interaction test

**Model.** Let two unlinked loci in a two-way admixed population carry causal variants $G_1, G_2$ (standardized genotypes) that act on a quantitative trait with main effects and an interaction,

$$Y = \beta_{G_1} G_1 + \beta_{G_2} G_2 + \beta_{\mathrm{int}G}\, G_1 G_2 + \varepsilon .$$

Let $L_1, L_2 \in \{0, 1, 2\}$ be the local ancestries (number of chromosomes of a given ancestry) at the segments containing $G_1$ and $G_2$, and consider the one-degree-of-freedom Wald test of $\beta_{\mathrm{int}L}$ in

$$Y = \beta_{L_1} L_1 + \beta_{L_2} L_2 + \beta_{\mathrm{int}L}\, L_1 L_2 + \varepsilon' .$$

**Statement** (Aschard, Gusev, Brown and Pasaniuc 2015, eqs. (1)–(8)). With $N$ individuals, the non-centrality parameters of the Wald tests of the true interaction, of the local-ancestry interaction, and of an interaction between tag SNPs $G_1^*, G_2^*$ are

$$S_S = N \rho^2(Y, G_1 \times G_2), \qquad S_L = S_S\, \rho_{LC}^2, \qquad S_G = S_S\, \rho_{GC}^2,$$

where $\rho_{LC}^2 = \rho^2(G_1 \times G_2,\ L_1 \times L_2)$ and $\rho_{GC}^2 = \rho^2(G_1 \times G_2,\ G_1^* \times G_2^*)$. Each statistic is $\chi^2_1$ under the null, and the power at level $\alpha$ is

$$\mathrm{Power} = 1 - F\!\left(\chi^2_{1, 1 - \alpha, 0}\ \middle|\ 1,\ S_\cdot\right),$$

with $F(\cdot \mid d, S)$ the non-central chi-square distribution function with $d$ degrees of freedom and non-centrality $S$. The three strategies are compared at thresholds $\alpha / \binom{n_S}{2}$, $\alpha / \binom{n_L}{2}$ and $\alpha / \binom{n_G}{2}$, with $n_S$ sequence variants, $n_L \approx 10^3$ ancestry segments and $n_G$ genotyped or imputed SNPs.

## Depends on

- [Wald's test](../../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/tendsto-in-distribution-wald-statistic.md): the $\chi^2_1$ null of each Wald statistic
- [Chi-square distribution](../../../../../Probability/distributions/continuous/chi-square-distribution/chi-square-measure.md)

## Proof depends on

- [Local power of the likelihood-ratio test](../../../../../Probability/hypothesis-testing/local-power-of-the-likelihood-ratio-test/tendsto-in-distribution-two-mul-log-like-2.md): the noncentral $\chi^2_1$ limit under local alternatives

## Expansion

Each test loses power by the squared correlation between the product it uses and the true product $G_1 G_2$, and gains by the smaller number of pairs it must correct for. Local ancestry tags a causal variant weakly — $\rho_{LC}$ depends on how differentiated the causal allele is between the ancestral populations — but there are only about $10^3$ segments, so $\binom{n_L}{2} \approx 5 \times 10^5$ pairs instead of $\binom{10^6}{2} = 5 \times 10^{11}$ SNP pairs or $2 \times 10^{14}$ pairs of sequence variants. The smaller threshold offsets about a factor $2$ in noncentrality (for $80\%$ power at $\alpha = 0.05$, about $38$ at $0.05/(5\times 10^5)$ against about $82$ at $0.05/(2\times 10^{14})$), so it compensates only $\rho_{LC}^2 \gtrsim 0.46$: the source finds the ancestry test more powerful than the sequence-based test only for $\rho_{LC} > 0.7$, and than the GWAS test with genotyped causal variants for $\rho_{LC} > 0.8$. When a segment harbors several causal variants with effects of the same sign, their contributions to the ancestry product add while a single tag SNP captures only one of them, which is why the advantage of the ancestry test grows with the number of causal variants per locus.

## Sources

- H. Aschard, A. Gusev, R. Brown and B. Pasaniuc, "Leveraging local ancestry to detect gene-gene interactions in genome-wide data", BMC Genetics 16 (2015), 124, Methods ("Genetic model", "A single major causal SNP per segment", "Multiple causal SNPs per segment"), eqs. (1)–(8), <https://doi.org/10.1186/s12863-015-0283-z>, PMCID PMC4619349.
