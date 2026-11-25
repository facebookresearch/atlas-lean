# Expected number of segregating sites in a neutral sample

For every real $\theta$ and every natural number $n$, the neutral ($\sigma = 0$)
[expected site frequency spectrum](expected-sfs.md) summed over the segregating classes
$1 \le i < n$ is

$$\sum_{i=1}^{n-1} \mathbb{E}\,\xi_i = \theta \sum_{i=1}^{n-1} \frac{1}{i},$$

both sums being empty, hence $0$, when $n \le 1$. For $\theta \ge 0$ this is Watterson's expected
number of segregating sites in a sample of $n$ gene copies. The sum leaves out the class $i = n$,
sites at which every sampled copy is derived, which are monomorphic in the sample, and the class
$i = 0$.

## Sources

- G. A. Watterson, *On the number of segregating sites in genetical models without
  recombination*, Theoret. Population Biol. 7 (1975), 256–276.
