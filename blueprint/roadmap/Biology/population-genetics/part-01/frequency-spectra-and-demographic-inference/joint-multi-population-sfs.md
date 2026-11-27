# Folding, ascertainment and subsampling of joint site-frequency spectra

Let $M[d_1, \dots, d_P]$ be the [expected joint allele-frequency spectrum](../../diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md) for samples of sizes $n_1, \dots, n_P$, obtained by independent binomial sampling from the [multi-population density](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md) $\phi$. When ancestral alleles cannot be determined, Gutenkunst, Hernandez, Williamson and Bustamante (2009, Methods) use the folded spectrum indexed by minor-allele frequency, and for ascertained data they modify the sampling equation to correct the bias. Written as operators on joint spectra, sampling is the linear map $\phi \mapsto M$; folding identifies the entries $(d_1, \dots, d_P)$ and $(n_1 - d_1, \dots, n_P - d_P)$ by summing them; and an ascertainment that keeps a site with probability $q(d)$ multiplies $M[d]$ by $q(d)$ before any renormalization. Since a binomial sample of size $n_i - 1$ is a uniformly random subsample of one of size $n_i$, the sampling map is consistent under subsampling in each population.

## Depends on

- [Expected joint allele-frequency spectrum and its Poisson likelihood](../../diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md)
- [Multi-population diffusion for the joint allele-frequency density](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md)
- [Folded site frequency spectrum](../../../coalescent-theory/expected-site-frequency-spectrum/folded-count.md)

## Expansion

1. Folding and ascertainment as linear maps on joint spectra.
2. Consistency of the sampling map under subsampling, from the hypergeometric reduction of binomial samples.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods, equation (3) and the folded and ascertained spectra. <https://doi.org/10.1371/journal.pgen.1000695>
