# Luria–Delbrück distribution

For a real number $m$ and a natural number $n$, let

$$p_n(m) = \sum_{k=0}^{n} e^{-m} \frac{m^k}{k!}\, c^{*k}(n),$$

with the [clone-size law](clone-prob.md) $c$ and its [convolution powers](conv-pow.md). For $m \ge 0$ it is the compound Poisson law of the number $n$ of mutants when the number of mutations is Poisson with mean $m$ and the clone sizes are independent with law $c$; since clones have size at least $1$, only $k \le n$ mutations contribute.

## Sources

- S. E. Luria and M. Delbrück, *Mutations of bacteria from virus sensitivity to virus resistance*, Genetics 28 (1943), 491–511.
- D. E. Lea and C. A. Coulson, *The distribution of the numbers of mutants in bacterial populations*, J. Genet. 49 (1949), 264–285.
