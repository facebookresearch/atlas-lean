# Divisive 2-means selection of conditioning haplotypes

In HMM-based phasing, each individual's haplotypes are resampled conditional on a set of $K$ conditioning haplotypes, chosen in each genomic window as the haplotypes closest in Hamming distance to the individual's current estimates. Comparing all $2N$ haplotypes pairwise costs $O(N^2)$ per window.

**Procedure.** Given $2N$ haplotypes over $L$ SNPs in a window and a cluster size $M \ll 2N$:
1. Recursively split the haplotypes with $k$-means for $k = 2$ (Euclidean distance on 0/1 vectors, at most ten Lloyd iterations), stopping when a cluster has fewer than $M$ members; this gives each haplotype a primary cluster.
2. "Top up" each leaf cluster with haplotypes from the closest leaf to a secondary cluster of exactly $M$ haplotypes.
3. For individual $i$, choose the $K$ conditioning haplotypes by minimum Hamming distance within the union of the secondary clusters of its two haplotypes (excluding individuals estimated to be IBD2 in the region).

**Complexity.** If each split halves a cluster, depth $d$ has $2^d$ clusters of size $2N/2^d$ (written $N/2^d$ below, absorbing constants), and each $k$-means iteration at depth $d$ costs $4\,(N/2^d)\,L$ per cluster. Summing over the $D = \log_2(N/M)$ levels $d = 0, \dots, D - 1$,

$$\sum_{d=0}^{D-1} 2^d\cdot\frac{4NL}{2^d} = 4NL\log_2\frac{N}{M} = O(N\log N)$$

for fixed $L$ and $M$, while the within-cluster Hamming comparisons cost $O(M^2)$ per cluster, independent of $N$.

## Remarks

In a short window, small Hamming distance is a proxy for recent shared ancestry, so the haplotypes most useful as HMM states are near neighbours, and a hierarchical partition finds them without all pairwise comparisons. Euclidean distance is used for clustering because the cluster means are fractional, while Hamming distance between binary vectors is used for the final selection because it can be computed with lookup tables; thinning to every eighth SNP from a random offset further cuts the clustering cost. Top-up guarantees that every haplotype is compared with exactly $M-1$ others even when a leaf is small.

## Depends on

- [The Li–Stephens copying model](../../../population-structure/li-stephens-haplotype-copying-model/hmm.md)

## Sources

- J. O'Connell, K. Sharp, N. Shrine et al., "Haplotype estimation for biobank-scale data sets", Nature Genetics (2016), Online Methods ("A sub-quadratic method for haplotype distance calculations", "Divisive K-Means clustering to partition the data"), <https://doi.org/10.1038/ng.3583> (PMC4926957).
