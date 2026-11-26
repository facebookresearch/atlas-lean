# Hypergeometric projection of the site-frequency spectrum

Let $\xi^{(n)}_i$, $1 \le i \le n - 1$, be the number of segregating sites at which exactly $i$ of $n$ sampled gene copies carry the derived allele, and let a subsample of $m < n$ copies be drawn uniformly without replacement from the sample. A site with $i$ derived copies among the $n$ then has $j$ derived copies in the subsample with the hypergeometric probability

$$h_{ij} = \frac{\binom{i}{j}\binom{n-i}{m-j}}{\binom{n}{m}},$$

so, taking expectations over the subsampling and the data,

$$E\bigl[\xi^{(m)}_j\bigr] = \sum_{i=1}^{n-1} h_{ij}\, E\bigl[\xi^{(n)}_i\bigr], \qquad 1 \le j \le m - 1,$$

where sites sent to $j = 0$ or $j = m$ are monomorphic in the subsample and dropped. This is a direct derivation; for $m = n - 1$ it is the downsampling identity $\Phi_{n+1}(i+1) = \frac{i+2}{n+2}\Phi_{n+2}(i+2) + \frac{n-i+1}{n+2}\Phi_{n+2}(i+1)$ used by Jouganous, Long, Ragsdale and Gravel (2017, Appendix A), and Gutenkunst, Hernandez, Williamson and Bustamante (2009, Results) project observed spectra to a smaller sample size to handle missing data. Under Kingman's coalescent, $E[\xi^{(n)}_i] = \theta/i$, and the identity $\sum_{i=1}^{n-1}\binom{i}{j}\binom{n-i}{m-j}/i = \binom{n}{m}/j$ for $1 \le j \le m - 1$ gives $E[\xi^{(m)}_j] = \theta/j$, the Kingman spectrum of the subsample, as the consistency of the coalescent under restriction requires.

## Depends on

- [Expected site frequency spectrum](../../../Biology/coalescent-theory/expected-site-frequency-spectrum/integral-sfs.md)
- [Consistency of the partition-valued coalescents](../../../Biology/coalescent-theory/partition-valued-kingman-coalescent/sum-time-law-restrict.md)

## Expansion

1. The subsampling operation and the hypergeometric law of the derived count in the subsample.
2. The projection of expected spectra, with the separate treatment of sites that become monomorphic.
3. The binomial identity $\sum_{i}\binom{i}{j}\binom{n-i}{m-j}/i = \binom{n}{m}/j$ and the Kingman check.
4. Preservation of expected spectra under every model whose genealogy of a subsample is the restriction of the genealogy of the sample.
5. Projection of observed spectra with missing genotypes to a common sample size, as a separate statement.

## Sources

- J. Jouganous, W. Long, A. P. Ragsdale and S. Gravel, Inferring the joint demographic history of multiple populations: beyond the diffusion approximation, Genetics 206 (2017), 1549–1567, Appendix A (downsampling formula). <https://doi.org/10.1534/genetics.117.200493>
- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, PLoS Genet. 5 (2009), e1000695, Results (projection of the data). <https://doi.org/10.1371/journal.pgen.1000695>
