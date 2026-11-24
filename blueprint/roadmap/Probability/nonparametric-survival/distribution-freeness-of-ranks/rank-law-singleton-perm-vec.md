# Each rank vector has probability one over n factorial

For $n \in \mathbb{N}$ and a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $r_\sigma = (\sigma(i) + 1)_{i=0}^{n-1} \in \mathbb{N}^n$ for its rank vector. Let $\mathrm{Rank}_n = \frac{1}{\# R_n} \sum_{r \in R_n} \delta_r$ be the uniform rank law, the uniform distribution on the finite set $R_n = \{r_\sigma\} \subseteq \mathbb{N}^n$ of these rank vectors. Then for every permutation $\sigma$ of $\{0, \dots, n-1\}$

$$\mathrm{Rank}_n(\{r_\sigma\}) = \frac{1}{n!}.$$

Distinct permutations have distinct rank vectors, so $R_n$ has exactly $n!$ elements.

## Sources

- J. Hájek, Z. Šidák and P. K. Sen, *Theory of Rank Tests*, 2nd ed., Academic Press (1999).
