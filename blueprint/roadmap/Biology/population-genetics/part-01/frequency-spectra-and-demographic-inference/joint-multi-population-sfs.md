# Joint site-frequency spectra of several populations

Gutenkunst, Hernandez, Williamson and Bustamante (2009, Methods) model the density $\phi(x_1, \dots, x_P, t)$ of derived mutations at population frequencies $x_1, \dots, x_P$ in $P$ populations by a multi-dimensional diffusion equation (their equation (1)) whose parameters encode population sizes, migration and selection; population splits and mergers change the dimension of $\phi$. The expected entry of the joint allele frequency spectrum for samples of sizes $n_1, \dots, n_P$ with derived counts $d_1, \dots, d_P$ is the $P$-dimensional integral of the probability of sampling those counts times the density of sites, and for resequencing data the sampling probabilities are independent binomials (their equation (3)):

$$M[d_1, \dots, d_P] = \int\prod_{i=1}^P\binom{n_i}{d_i}x_i^{d_i}(1 - x_i)^{n_i - d_i}\,\phi(x_1, \dots, x_P)\,dx_1\cdots dx_P.$$

When ancestral alleles cannot be determined, the folded spectrum indexed by minor-allele frequency is used, and for ascertained data the sampling equation is modified to correct the bias (same section). Written as operators on joint spectra, sampling is the linear map $\phi \mapsto M$ above; folding identifies the entries $(d_1, \dots, d_P)$ and $(n_1 - d_1, \dots, n_P - d_P)$ by summing them; and an ascertainment that keeps a site with probability $q(d)$ multiplies $M[d]$ by $q(d)$ before any renormalization. Since a binomial sample of size $n_i - 1$ is a uniformly random subsample of one of size $n_i$, the sampling map is consistent under subsampling in each population.

## Depends on

- [Expected site frequency spectrum under the Poisson random field](../../diffusion-theory/poisson-random-field-model/expected-sfs.md)
- [Folded site frequency spectrum](../../../coalescent-theory/expected-site-frequency-spectrum/folded-count.md)

## Expansion

1. The multi-population diffusion for the density of segregating sites, and the change of dimension at splits and mergers.
2. The binomial sampling map from densities to joint spectra.
3. Folding and ascertainment as linear maps on joint spectra.
4. Consistency of the sampling map under subsampling, from the hypergeometric reduction of binomial samples.

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Methods, equations (1)–(3). <https://doi.org/10.1371/journal.pgen.1000695>
