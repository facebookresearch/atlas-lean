# Missing data in spectrum-based coalescent inference

Spectrum-based inference compares an observed site-frequency spectrum with its expectation for a fixed number of sampled gene copies, so sites at which some genotypes are missing do not contribute a spectrum entry of the full sample size. Gutenkunst, Hernandez, Williamson and Bustamante (2009, Results) handle missing data by projecting the observed spectrum to a smaller common sample size, and Nielsen, Paul, Albrechtsen and Song (2011, Figure 4) likewise subsample all methods in their comparison to $20$ chromosomes because one method leaves missing data. Under the hypergeometric projection, each site with at least $m$ observed copies contributes to the spectrum of size $m$, and the expected projected spectrum is the model spectrum for $m$ copies, provided the pattern of missing genotypes does not depend on the unobserved alleles. Replacing missing or uncertain genotypes by called genotypes biases the spectrum instead: in simulated low-coverage data (mean depth $4\times$, error rate $0.003$), spectra built from called genotypes, whether from the most probable genotype or only from calls with posterior probability above $0.95$, overestimate the number of singletons, and priors or filters biased against singletons introduce other biases (Nielsen et al. 2011, Figure 4 and text). Their alternative, carrying the uncertainty forward as per-site posterior probabilities of the sample allele frequency, is stated separately in [EM estimation of the sample allele frequency spectrum](../../../statistical-genetics/genotype-likelihoods-from-sequencing-data/em-estimate-of-the-allele-frequency-spectrum.md) and is not restated here.

## Depends on

- [Hypergeometric projection of the site-frequency spectrum](../../expected-site-frequency-spectrum/spectrum-subsampling-operator.md)

## Expansion

1. Missing genotypes per site and the number of observed gene copies at each site.
2. Projection of every site with at least $m$ observed copies to sample size $m$, and the condition on the missingness pattern under which the expected projected spectrum equals the model spectrum.
3. The bias of spectra from called genotypes at low depth, with the excess of singletons in the simulation of Nielsen et al.

## Sources

- R. Nielsen, J. S. Paul, A. Albrechtsen and Y. S. Song, Genotype and SNP calling from next-generation sequencing data, Nat. Rev. Genet. 12 (2011), 443–451, Figure 4 and the section on population-genetic inference. <https://doi.org/10.1038/nrg2986>
- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Results. <https://doi.org/10.1371/journal.pgen.1000695>
