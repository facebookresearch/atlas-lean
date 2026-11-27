# Expected joint allele-frequency spectrum and its Poisson likelihood

Let $\phi(x_1, \dots, x_P)$ be the [joint density of derived mutations](multipopulation-diffusion-with-migration-and-admixture.md) at present. Sample $n_i$ sequences from population $i$. For resequencing data, the expected number of diallelic sites at which the derived allele appears in exactly $d_i$ of the $n_i$ samples of each population $i$ is

$$M[d_1, \dots, d_P] = \int_0^1 \!\cdots\! \int_0^1 \prod_{i=1}^P \binom{n_i}{d_i} x_i^{d_i} (1 - x_i)^{n_i - d_i}\, \phi(x_1, \dots, x_P)\, dx_1 \cdots dx_P .$$

For $P = 1$ this is the [expected site frequency spectrum](expected-sfs.md) of the Poisson random field.

Let $S[d_1, \dots, d_P]$ be the observed joint spectrum and $\Theta$ the demographic parameters on which $M$ depends. Let

$$\mathcal D \subseteq \{0, \dots, n_1\} \times \cdots \times \{0, \dots, n_P\}$$

be the set of observable cells: the full grid of joint counts with the masked cells removed (in practice at least the all-zero corner $(0, \dots, 0)$ and the all-derived corner $(n_1, \dots, n_P)$). If polymorphisms are unlinked, the entries $S[d]$, $d \in \mathcal D$, are independent Poisson variables with means $M[d]$, so

$$L(\Theta \mid S) = \prod_{(d_1, \dots, d_P) \in \mathcal D} \frac{e^{-M[d_1,\dots,d_P]}\, M[d_1,\dots,d_P]^{S[d_1,\dots,d_P]}}{S[d_1,\dots,d_P]!} ,$$

one Poisson factor per spectrum entry, $|\mathcal D|$ factors in all, at most $\prod_i (n_i + 1)$. For two populations each sampled twice the grid has $9$ cells before masking. With linked sites, $L$ is a composite likelihood: still useful for point estimation, but variances must come from simulation or resampling.

## Depends on

- [Expected site frequency spectrum under the Poisson random field](expected-sfs.md)
- [Multi-population diffusion for the joint allele-frequency density](multipopulation-diffusion-with-migration-and-admixture.md)

## Proof depends on

Its proof is binomial sampling given the population frequencies and the colouring theorem for Poisson random fields, as the Expansion describes.

## Expansion

Given population frequencies $x_i$, the $n_i$ sampled copies in population $i$ are independent Bernoulli($x_i$) draws, independent across populations, which gives the product of binomial probabilities. Integrating against the Poisson intensity $\phi$ thins the Poisson random field of unlinked sites into independent Poisson counts, one per cell $d$ of the grid (Poisson colouring theorem), and restricting to the cells of $\mathcal D$ gives the product likelihood.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, *Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data*, PLoS Genet. 5 (2009), e1000695, <https://doi.org/10.1371/journal.pgen.1000695>, PMCID PMC2760211, Methods: Equation 3 (expected spectrum from binomial sampling) and Equation 4 (Poisson likelihood), "Likelihood-based inference".
