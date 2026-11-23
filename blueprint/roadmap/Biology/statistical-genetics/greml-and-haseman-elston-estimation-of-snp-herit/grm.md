# Genetic relationship matrix

For a real $N \times M$ genotype matrix $X$ (rows are individuals, columns are markers), the
genetic relationship matrix (GRM) is the $N \times N$ matrix with entries

$$
A_{ij} = \frac{1}{M} \sum_{k=1}^{M} X_{ik} X_{jk}, \qquad \text{that is,} \qquad
A = \frac{1}{M} X X^\top.
$$

With no markers ($M = 0$) the sum is empty and, with the convention $x/0 = 0$, $A = 0$. The
definition applies to every real matrix; when the columns of $X$ are genotypes standardized marker
by marker (centred and scaled to unit variance), $A$ is the GRM of Yang et al. (2010).

## Sources

- J. Yang, B. Benyamin, B. P. McEvoy, et al., *Common SNPs explain a large proportion of the
  heritability for human height*, Nat. Genet. 42 (2010), 565–569.
