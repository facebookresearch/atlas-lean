# Allele-frequency estimate of a marker

For a real $N \times M$ genotype matrix $C$ (variant-allele counts) and a marker $j$, the allele-frequency estimate is

$$\hat p_j = \frac{\mu_j}{2}, \qquad \mu_j = \frac{1}{N} \sum_{i=1}^{N} C_{ij},$$

with the convention $x/0 = 0$ when $N = 0$. For $N > 0$ and diploid counts in $\{0, 1, 2\}$ this is the sample frequency of the variant allele.
