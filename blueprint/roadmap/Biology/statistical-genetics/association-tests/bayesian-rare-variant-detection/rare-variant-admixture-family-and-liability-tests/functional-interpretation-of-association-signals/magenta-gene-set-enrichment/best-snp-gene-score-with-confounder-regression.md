# Best-SNP gene score with confounder regression and the Šidák alternative

Let gene $g$ be assigned the set $I(g)$ of SNPs lying within extended gene boundaries (in MAGENTA, 110 kb upstream of the most extreme transcription start and 40 kb downstream of the most extreme transcription end), and let $p_i$ be the association p-value of SNP $i$ from a genome-wide association study or meta-analysis. The best-SNP gene score is

$$p_g^{\min} = \min_{i \in I(g)} p_i,$$

converted to a z-score $z_g$ through the standard normal quantile function. Because $p_g^{\min}$ is stochastically smaller for genes with more SNPs or more independent LD units, MAGENTA regresses $z_g$ across all genes on gene properties $v_{g1}, \dots, v_{gq}$ (physical gene size, number of SNPs per kilobase, number of independent SNPs, number of recombination hotspots, genetic distance, and LD-unit distance normalized to the extended gene length) by step-wise multiple linear regression,

$$z_g = \sum_{r} \beta_r v_{gr} + \varepsilon_g,$$

with no intercept (the source's Equation (2)), and uses the residual $\varepsilon_g = z_g - \sum_r \hat\beta_r v_{gr}$ (Equation (3)) as the corrected gene score, with a corrected gene p-value read from the standard normal distribution. The analytical alternative is Šidák's correction for the $N_g = |I(g)|$ SNP tests,

$$p_g^{\mathrm{Sidak}} = 1 - \big(1 - p_g^{\min}\big)^{N_g},$$

or the modification $1 - (1 - p_g^{\min})^{(N_g + 1)/2}$, which assumes that about half of the SNPs in a region are in tight linkage disequilibrium.

## Expansion

If the $N_g$ SNP p-values were independent and uniform under the null, $\mathbb P(p_g^{\min} \le x) = 1 - (1-x)^{N_g}$, so Šidák's formula gives an exactly uniform gene p-value; linkage disequilibrium makes the effective number of tests smaller than $N_g$, and the correction is then conservative, which motivates the $(N_g+1)/2$ heuristic. The regression approach estimates the dependence of the best-SNP score on gene properties empirically from the genome-wide data, without genotypes, and Segrè et al. selected the predictors by applying it to 1,000 phenotype permutations of a genome-wide association study, in which every property except genetic distance was significant in roughly half or all of the permutations, so the other five were retained. The best-SNP score is most powerful for genes with one main associated haplotype.

## Sources

- A. V. Segrè, DIAGRAM Consortium, MAGIC investigators, L. Groop, V. K. Mootha, M. J. Daly, D. Altshuler, "Common inherited variation in mitochondrial genes is not enriched for associations with type 2 diabetes or related glycemic traits", PLoS Genetics 6 (2010), e1001058, <https://doi.org/10.1371/journal.pgen.1001058> (PMC2920848), Materials and Methods, MAGENTA Steps 1–3 (Equations 1–5).
