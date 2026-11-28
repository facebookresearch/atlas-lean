# LD-weighted genetic relationship matrix (LDAK)

Let $x_{ik} \in \{0,1,2\}$ be the genotype of individual $i$ at SNP $k = 1, \dots, m$, with allele frequency $p_k \in (0,1)$. Given nonnegative SNP weights $w_k$, not all zero, the LD-adjusted kinship matrix is

$$K_{ij} = \frac{1}{\sum_{k} w_k}\sum_{k=1}^{m} w_k\,\frac{(x_{ik} - 2p_k)(x_{jk} - 2p_k)}{2p_k(1-p_k)},$$

and it replaces the unweighted [genetic relationship matrix](grm.md) (the case $w_k \equiv 1$) in the GREML model $y \sim \mathcal N(X\beta, \sigma_g^2 K + \sigma_e^2 I)$. In LDAK the weights are computed from local linkage disequilibrium so that a SNP's weight is inversely related to how strongly it is correlated with nearby SNPs: SNPs in high-LD regions, which redundantly tag the same causal variation, are down-weighted, and SNPs in low-LD regions are up-weighted, so that every genomic region contributes in proportion to its tagged variation rather than to its number of SNPs. The standardization by $2p_k(1-p_k)$ corresponds to effect sizes whose variance scales as $[2p_k(1-p_k)]^{-1}$ (the "$\alpha = -1$" model).

## Depends on

- [Genetic relationship matrix](grm.md)

## Expansion

Under the unweighted model each standardized SNP contributes equally, so a causal variant in a region of high LD is tagged by many SNPs and its variance is counted many times, while causal variants in low-LD regions are under-tagged; heritability estimates then depend on how the LD around causal variants compares with the genome average. Weighting by inverse local LD equalizes tagging. Evans et al. show the price of the correction in whole-genome sequence data: when all SNPs including very rare ones are used, the LD-based weights become near zero for common SNPs and very large for rare SNPs, giving underestimates when causal variants are common and overestimates when they are very rare, whereas with common SNPs only LDAK removes the overestimation that unweighted GREML shows for common causal variants. Evans et al. also fit one LD-weighted matrix per allele-frequency stratum (multi-component LDAK), with weights estimated over the union of all SNPs.

## Sources

- D. Speed, G. Hemani, M. R. Johnson, D. J. Balding, "Improved heritability estimation from genome-wide SNPs", American Journal of Human Genetics 91 (2012), 1011–1021, <https://doi.org/10.1016/j.ajhg.2012.10.010>.
- L. M. Evans, R. Tahmasbi, S. I. Vrieze, et al., "Comparison of methods that use whole genome data to estimate the heritability and genetic architecture of complex traits", Nature Genetics 50 (2018), <https://doi.org/10.1038/s41588-018-0108-x> (PMC5934350), Online Methods "Single- and multi-component LD-Adjusted Kinships (LDAK-SC and LDAK-MS)" and Results.
