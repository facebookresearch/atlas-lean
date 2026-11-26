# Negative-binomial test for allele-specific reporter activity

**Setting.** In a massively parallel reporter assay, a library of DNA fragments, each carrying a known allele of a candidate variant and a barcode, is transfected into cells; the activity of a fragment is read as its RNA barcode count relative to its abundance in the plasmid pool. For a biallelic SNP $j$, fragments overlapping it are labeled by the allele they carry.

**Statement** (Morova et al. 2023, Materials and Methods, "Testing bi-allelic activity"). For fragment $i$ let $Y_i$ be its RNA read count, $P_i$ its plasmid DNA read count, and $X_{ij} \in \{0, 1\}$ the indicator that the fragment carries the alternative rather than the reference allele of SNP $j$. Fit the negative-binomial regression with logarithmic link and plasmid count as offset,

$$\log \mathbb{E}(Y_i) = \beta_{0j} + \beta_{1j} X_{ij} + \log P_i ,$$

so that $\beta_{0j}$ is the log expression per plasmid of the reference allele and $\beta_{1j}$ the log fold change of expression per plasmid between the alternative and the reference allele; allele-specific activity is the test of $\beta_{1j} = 0$. Only SNPs with more than $15$ distinct plasmids carrying each allele are tested.

## Depends on

- [Negative binomial mass function with size and mean](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)

## Remarks

The offset $\log P_i$, with coefficient fixed at one, makes the model one for the rate $\mathbb{E}(Y_i)/P_i$, that is activity per plasmid, so differences in how often a fragment entered the library do not masquerade as differences in activity; estimating a free coefficient for $\log P_i$ instead would let the library composition absorb part of the allelic effect. The negative binomial rather than the Poisson is needed because replicate counts are overdispersed: barcode counts vary between fragments carrying the same allele far more than Poisson sampling allows, and fitting a Poisson would make the standard error of $\hat\beta_{1j}$ too small and the test anticonservative. Because the two allele groups consist of different fragments, the comparison also absorbs fragment-to-fragment variation in genomic context only on average, which is why the type I error of the procedure is calibrated empirically on fragments that carry no tested variant.

## Sources

- T. Morova, Y. Ding, C.-F. Huang, F. Sar, T. Schwarz, C. Giambartolomei et al., "Optimized high-throughput screening of non-coding variants identified from genome-wide association studies", Nucleic Acids Research 51 (2023), e18, Materials and Methods ("Testing bi-allelic activity", "Empirical type-I error for NBR"), <https://doi.org/10.1093/nar/gkac1198>, PMCID PMC9943666.
