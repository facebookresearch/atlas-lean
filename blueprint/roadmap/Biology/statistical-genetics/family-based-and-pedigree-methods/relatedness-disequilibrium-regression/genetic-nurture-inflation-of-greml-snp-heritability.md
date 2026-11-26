# Genetic-nurture inflation of GREML-SNP heritability

Consider a SNP with direct effect $\delta$ on the proband's phenotype and parental genetic nurture effect $\eta$ (the effect of the same allele carried by a parent, acting through the environment it provides). An allele transmitted to the proband is also carried by a parent, so its marginal effect on the proband's phenotype is $\delta + \eta$.

**Claim.** GREML-SNP, which models phenotypic covariance by the SNP relationship matrix of the probands alone, cannot separate the direct variance, proportional to $\delta^2$, from the variance explained by direct plus nurture effects of transmitted alleles, proportional to $(\delta + \eta)^2$. If every SNP has $\eta = \lambda \delta$, the GREML-SNP estimate targets

$$h^2_{\mathrm{GREML}} \approx (1 + \lambda)^2\, h^2$$

instead of the direct heritability $h^2$, whereas [RDR-SNP](rdr-variance-decomposition-and-covariance-model.md), which also fits the parental relatedness matrices, targets $h^2$.

## Depends on

- [RDR variance decomposition and covariance model](rdr-variance-decomposition-and-covariance-model.md)
- [GREML covariance matrix](../../greml-and-haseman-elston-estimation-of-snp-herit/greml-cov.md)

## Expansion

Only transmitted alleles enter the proband's genotype, so any regression of proband phenotype on proband genotype loads the nurture effect onto the genotype; the covariance between relatives then scales with $(\delta+\eta)^2$. RDR breaks the confounding by adding $R_{\mathrm{par}}$ and $R_{o,\mathrm{par}}$, which absorb $v_{e\sim g}$ and $c_{g,e}$. In UK Biobank simulations with direct effects explaining $20\%$ and $\eta = \delta/3$, transmitted alleles explained $(1 + 1/3)^2 \times 20\% \approx 35.56\%$; the mean GREML-SNP estimate was $35.15\%$ and the mean RDR-SNP estimate $19.70\%$. Both methods are additionally biased when the causal variants differ from the SNPs used to build the relationship matrices.

## Sources

- A. I. Young, M. L. Frigge, D. F. Gudbjartsson, et al., "Relatedness disequilibrium regression estimates heritability without environmental bias", *Nature Genetics* (2018), <https://doi.org/10.1038/s41588-018-0178-9> (PMC6130754; section "GREML-SNP estimates are biased by genetic nurturing"; theory in the Supplementary Note).
