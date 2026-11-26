# Expected joint allele-frequency spectrum and its Poisson likelihood

Let $\phi(x_1, \dots, x_P)$ be the [joint density of derived mutations](multipopulation-diffusion-with-migration-and-admixture.md) at present. Sample $n_i$ sequences from population $i$. For resequencing data, the expected number of diallelic sites at which the derived allele appears in exactly $d_i$ of the $n_i$ samples of each population $i$ is

$$M[d_1, \dots, d_P] = \int_0^1 \!\cdots\! \int_0^1 \prod_{i=1}^P \binom{n_i}{d_i} x_i^{d_i} (1 - x_i)^{n_i - d_i}\, \phi(x_1, \dots, x_P)\, dx_1 \cdots dx_P .$$

For $P = 1$ this is the [expected site frequency spectrum](expected-sfs.md) of the Poisson random field.

Let $S[d_1, \dots, d_P]$ be the observed joint spectrum and $\Theta$ the demographic parameters on which $M$ depends. If polymorphisms are unlinked, the entries of $S$ are independent Poisson variables with means $M$, so

$$L(\Theta \mid S) = \prod_{i=1}^P \prod_{d_i = 0}^{n_i} \frac{e^{-M[d_1,\dots,d_P]}\, M[d_1,\dots,d_P]^{S[d_1,\dots,d_P]}}{S[d_1,\dots,d_P]!} ,$$

a product of $\prod_i (n_i + 1)$ Poisson factors (entries that cannot be observed, such as the all-zero and all-$n$ corners, are masked in practice). With linked sites, $L$ is a composite likelihood: still useful for point estimation, but variances must come from simulation or resampling.

## Depends on

- [Expected site frequency spectrum under the Poisson random field](expected-sfs.md)
- [Multi-population diffusion for the joint allele-frequency density](multipopulation-diffusion-with-migration-and-admixture.md)

## Expansion

Given population frequencies $x_i$, the $n_i$ sampled copies in population $i$ are independent Bernoulli($x_i$) draws, independent across populations, which gives the product of binomial probabilities. Integrating against the Poisson intensity $\phi$ thins the Poisson random field of sites into independent Poisson counts per spectrum cell (Poisson colouring theorem), giving the product likelihood.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, *Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data*, PLoS Genet. 5 (2009), e1000695, <https://doi.org/10.1371/journal.pgen.1000695>, PMCID PMC2760211, Methods: Equation 3 (expected spectrum from binomial sampling) and Equation 4 (Poisson likelihood), "Likelihood-based inference".
