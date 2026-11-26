# Normalized intrahost heterozygosity of a polygenomic infection

**Setting.** A malaria infection is *polygenomic* when it carries more than one parasite genotype. Genotyping a panel of biallelic SNPs (a molecular barcode) calls a site heterozygous when both alleles are present in the infection. Two processes produce polygenomic infections: *superinfection*, in which the strains are independent draws from the parasite population, and *cotransmission*, in which they are co-inherited from one mosquito and therefore related.

**Definition** (Wong et al. 2022, eq. (2)). Let $H_{\mathrm{poly}}$ be the observed heterozygosity of a polygenomic sample, the number of heterozygous sites divided by the number of non-missing sites, and let $H_{\mathrm{sup}}$ be the heterozygosity expected of a superinfection of complexity two, estimated by repeatedly drawing two distinct monogenomic barcodes from the same population and year and dividing their number of discordant alleles by the number of sites that are non-missing and homozygous in both. Following Wright's definition of the inbreeding coefficient as a correlation of uniting gametes, the metric is the normalized deficit of heterozygosity

$$R_H = 1 - \frac{H_{\mathrm{poly}}}{H_{\mathrm{sup}}} .$$

Its expected values under the two processes are: $R_H = 0$ for a superinfection of complexity two and, in the limit of rare alleles, $R_H = -0.5$ for complexity three and $R_H = -1$ for complexity four; and $R_H > 0$ for cotransmission, rising in the source's transmission model to about $0.40$, $0.60$ and $0.70$ after the first, second and third cotransmission event in a chain initiated by a complexity-two superinfection. Averages over a region are combined across sampling years by inverse-variance weighting, $\bar x = \sum_i x_i / \sigma_i^2 \big/ \sum_i 1/\sigma_i^2$, with the per-year variances obtained by bootstrap.

## Proof sketch

The normalization is what distinguishes $R_H$ from $F_{WS}$, which divides intrahost heterozygosity by the heterozygosity of the whole population: the reference here is the heterozygosity that two unrelated strains from the same population would show, so $R_H$ measures relatedness in excess of the local baseline rather than diversity relative to the population. For $k$ unrelated strains at a site with minor-allele frequency $p$ the probability of a heterozygous call is $1 - p^k - (1 - p)^k$, which for rare alleles is about $k/2$ times its value at $k = 2$; this gives the quoted negative values $1 - 3/2$ and $1 - 2$ at complexities three and four, so negative $R_H$ indicates more strains rather than less relatedness. Related strains share stretches of genome identical by descent and therefore produce fewer discordant sites than independent draws, giving positive $R_H$. Individual infections scatter widely around these expectations, so classification of single samples uses a Bayes factor rather than the point value.

## Sources

- W. Wong, S. Volkman, R. Daniels, S. Schaffner, M. Sy, Y. D. Ndiaye et al., "$R_H$: a genetic metric for measuring intrahost Plasmodium falciparum relatedness and distinguishing cotransmission from superinfection", PNAS Nexus 1 (2022), pgac187, Results (Figure 4A) and Materials and methods ("Inverse-variance weighting", "$R_H$", "Evaluating $R_H$"), eqs. (1)–(3), <https://doi.org/10.1093/pnasnexus/pgac187>, PMCID PMC9552330.
