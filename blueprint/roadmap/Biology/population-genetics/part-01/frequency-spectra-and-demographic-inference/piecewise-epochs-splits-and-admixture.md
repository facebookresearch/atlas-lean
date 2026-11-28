# Composition of the joint frequency density across demographic epochs and events

In diffusion methods for demographic inference, a history made of epochs with constant parameters, separated by population splits and admixture events, acts on the density $\phi$ of derived alleles at joint population frequencies. Within an epoch $\phi$ evolves by the [multi-population diffusion](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md), whose parameters change with population sizes and migration rates, and admixture, splits and the removal of a population act on $\phi$ as stated there (Gutenkunst, Hernandez, Williamson and Bustamante 2009, Methods, equations (1)–(2)). The following composition rules are derived from these operations. If $\Phi_e$ denotes the map that evolves a density through epoch $e$, the density after epochs $e_1, \dots, e_k$ with events $E_1, \dots, E_{k-1}$ between them is $\Phi_{e_k}E_{k-1}\cdots E_1\Phi_{e_1}\phi_0$, by the flow property of the epoch maps: each $\Phi_e$ solves the diffusion equation of its epoch together with the injection of new mutations, so it is an affine map, and solutions over consecutive subintervals of an epoch compose to the solution over the whole epoch (the Chapman–Kolmogorov property of the transition laws alone would omit the mutations entering during the epoch); each event is the pushforward of $\phi$ under the deterministic map $(x_1, \dots, x_P) \mapsto (x_1, \dots, x_P, fx_1 + (1 - f)x_2)$ followed, where populations end, by marginalization. The [expected joint spectrum](../../diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md) is then obtained by binomial sampling from the final density.

## Depends on

- [Expected joint allele-frequency spectrum and its Poisson likelihood](../../diffusion-theory/poisson-random-field-model/expected-joint-allele-frequency-spectrum-and-poisson-likelihood.md)
- [Multi-population diffusion for the joint allele-frequency density](../../diffusion-theory/poisson-random-field-model/multipopulation-diffusion-with-migration-and-admixture.md)
- [Piecewise-constant population-size history](../../../coalescent-theory/site-frequency-spectrum-under-variable-populatio/piecewise-history.md)

## Expansion

1. Piecewise evolution families and their composition across epochs.
2. Splits and admixture as pushforwards under linear maps on frequency vectors, producing densities singular with respect to Lebesgue measure.
3. The coalescent counterparts of admixture pulses.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods, equations (1)–(3). <https://doi.org/10.1371/journal.pgen.1000695>
