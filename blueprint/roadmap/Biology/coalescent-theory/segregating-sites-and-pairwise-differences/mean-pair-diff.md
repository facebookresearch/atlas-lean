# Mean number of pairwise differences

For a natural number $n$ and real functions $D_s$ on a set $\Omega$, indexed by the [pairs](sample-pairs.md) $s$ of genes of a sample of size $n$, the mean number of pairwise differences is the function

$$\pi = \binom{n}{2}^{-1} \sum_{s} D_s,$$

the sum running over the pairs of the sample (so $\pi = 0$ when $n \le 1$). Here $D_s$ is the number of sites at which the two sequences of the pair $s$ differ.

## Sources

- F. Tajima, *Evolutionary relationship of DNA sequences in finite populations*, Genetics 105 (1983), 437–460.
