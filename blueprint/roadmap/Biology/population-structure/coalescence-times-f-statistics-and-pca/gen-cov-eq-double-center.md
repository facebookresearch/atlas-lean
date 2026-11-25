# Genotype covariance as double-centred pairwise differences

For every real matrix $Z$ indexed by a finite set $\iota$ of samples and a finite set $S$ of $L$ loci, and all $i, j \in \iota$,

$$C_{ij} = \frac{(\mathcal{D} d)_{ij}}{2L},$$

where $C$ is the [sample covariance](gen-cov.md), $d$ the [pairwise-difference matrix](pair-diff.md) and $\mathcal{D}$ the [double centring](double-center.md), with the convention $x/0 = 0$ (McVean 2009).

## Sources

- G. McVean, *A genealogical interpretation of principal components analysis*, PLoS Genet. 5 (2009), e1000686.
