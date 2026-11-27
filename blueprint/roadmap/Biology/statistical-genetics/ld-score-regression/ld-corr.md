# Normalized cross product of genotype markers

For a real $N \times M$ genotype matrix $X$ and markers $j, k$, the normalized cross product is

$$r_{jk} = \frac{1}{N} \sum_{i=1}^{N} X_{ij} X_{ik},$$

with the convention $x/0 = 0$ when $N = 0$. For a [standardized](is-standardized.md) genotype matrix with $N > 0$ it is the sample correlation of the two markers; in general it is only a scale-dependent dot product.
