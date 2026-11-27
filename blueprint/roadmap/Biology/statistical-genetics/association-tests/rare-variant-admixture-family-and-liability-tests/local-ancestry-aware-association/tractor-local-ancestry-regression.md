# Tractor local ancestry regression

Consider two-way admixed individuals with phased genotypes and local ancestry calls. At a biallelic SNP, for individual $i$ let $X_{1i} \in \{0, 1, 2\}$ be the number of haplotypes of the index ancestry at the locus, and let $X_{2i}$ and $X_{3i}$ be the numbers of copies of the risk allele carried on haplotypes of the first and of the second ancestry, respectively (so $X_{2i} + X_{3i}$ is the ordinary allele count). For a binary phenotype $Y_i$ and covariates $X_{4i}, \dots, X_{ki}$ (age, sex, global ancestry or principal components), the Tractor model is

$$\operatorname{logit} \Pr(Y_i = 1) = b_0 + b_1 X_{1i} + b_2 X_{2i} + b_3 X_{3i} + \sum_{j=4}^{k} b_j X_{ji} .$$

The coefficients $b_2$ and $b_3$ are ancestry-specific allelic effects. Association of the SNP is tested by a likelihood-ratio test of this model against the model without $X_2$ and $X_3$, a 2-degree-of-freedom test that allows the allelic effect to differ between ancestries. For a continuous phenotype the same design is used in linear regression, and for more ancestries one adds a local-ancestry dosage term and an ancestry-specific allele count per additional ancestry.

## Expansion

The standard GWAS model is the submodel with $b_1 = 0$ and $b_2 = b_3$, using only $X_2 + X_3$. Including the local-ancestry dosage $X_1$ absorbs allele-frequency differences between ancestral backgrounds at the locus itself, so ancestry-related stratification is controlled at the genotype level rather than only through genome-wide covariates. Splitting the allele count by ancestry gains power when effects or frequencies differ between ancestries and localizes signal using the different linkage disequilibrium of each background; the price is one extra degree of freedom per ancestry, which can lower power when effects are identical. The source simulates African American cohorts with local ancestry inference about 98% accurate and finds well-calibrated false positive rates.

## Sources

- E. G. Atkinson, A. X. Maihofer, M. Kanai, A. R. Martin, K. J. Karczewski, et al., "Tractor uses local ancestry to enable the inclusion of admixed individuals in GWAS and to boost power", *Nature Genetics* 53 (2021), 195–204, introductory model statement and Methods section "GWAS power simulations incorporating local ancestry", <https://doi.org/10.1038/s41588-020-00766-y> (PMC7867648).
