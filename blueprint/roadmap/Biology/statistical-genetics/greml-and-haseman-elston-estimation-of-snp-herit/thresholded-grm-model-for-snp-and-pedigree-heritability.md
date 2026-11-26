# Thresholded-GRM model for joint SNP and pedigree heritability

Let a sample of $n$ individuals, possibly including close relatives, have phenotype vector $y \in \mathbb R^n$, fixed-effect design $X$ and a [genetic relationship matrix](grm.md) $A$ computed from genome-wide SNPs. For a relatedness threshold $t > 0$ define the thresholded matrix

$$A^{(t)}_{ij} = \begin{cases} A_{ij} & \text{if } A_{ij} \ge t, \\ 0 & \text{otherwise}, \end{cases}$$

which retains only pairs of close relatives (diagonal entries, being close to $1$, are retained). The two-component variance model is

$$y \sim \mathcal N\big(X\beta,\; \sigma_g^2 A + \sigma_t^2 A^{(t)} + \sigma_e^2 I\big),$$

fitted by restricted maximum likelihood. With $V_P = \sigma_g^2 + \sigma_t^2 + \sigma_e^2$, the quantities

$$h^2_{\mathrm{SNP}} = \frac{\sigma_g^2}{V_P}, \qquad h^2_{\mathrm{IBS}>t} = \frac{\sigma_t^2}{V_P}, \qquad h^2 \approx h^2_{\mathrm{SNP}} + h^2_{\mathrm{IBS}>t}$$

estimate the variance tagged by the SNPs, the additional variance captured only through close relatives, and the total narrow-sense heritability.

## Depends on

- [Genetic relationship matrix](grm.md)
- [GREML covariance matrix](greml-cov.md)

## Expansion

For distantly related pairs genotype similarity at the SNPs reflects only linkage disequilibrium with causal variants, so the full matrix $A$ captures the SNP-tagged variance. Close relatives share long identical-by-descent segments that also carry untyped and rare causal variants, so their phenotypic covariance exceeds what $A$ predicts; the thresholded matrix, nonzero only for those pairs, absorbs the excess. The total therefore resembles pedigree heritability and inherits its weaknesses: shared environment among cohabiting relatives is confounded with $\sigma_t^2$ unless modeled. Evans et al. compare this approach (thresholds $0.05$ and $0.1$) with single-component, MAF-stratified and LD- and MAF-stratified GREML, LD-weighted kinships and LD score regression on simulated whole-genome data.

## Sources

- N. Zaitlen, P. Kraft, N. Patterson, et al., "Using extended genealogy to estimate components of heritability for 23 quantitative and dichotomous traits", PLoS Genetics 9 (2013), e1003520, <https://doi.org/10.1371/journal.pgen.1003520>.
- L. M. Evans, R. Tahmasbi, S. I. Vrieze, et al., "Comparison of methods that use whole genome data to estimate the heritability and genetic architecture of complex traits", Nature Genetics 50 (2018), <https://doi.org/10.1038/s41588-018-0108-x> (PMC5934350), Online Methods "Extended Genealogy with Thresholded GRMs".
