# McVean's theorem on expected genotype covariance

For every [genealogical model](mc-vean-model.md) on a measure $\mu$ with $L$ loci, mutation rate $\theta$ and coalescence times $t$, and all samples $i, j$,

$$\int C_{ij} \, d\mu = \frac{\theta}{2L}\, (\mathcal{D} t)_{ij},$$

where $C$ is the [sample covariance](gen-cov.md) of the random genotypes and $\mathcal{D}$ the [double centring](double-center.md), with the convention $x/0 = 0$: the expected PCA matrix is determined by the expected pairwise coalescence times (McVean 2009).

## Sources

- G. McVean, *A genealogical interpretation of principal components analysis*, PLoS Genet. 5 (2009), e1000686.
