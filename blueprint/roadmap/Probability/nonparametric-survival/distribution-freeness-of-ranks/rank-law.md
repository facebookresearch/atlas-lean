# Uniform law on rank vectors

For $n \in \mathbb{N}$ and a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $r_\sigma = (\sigma(i) + 1)_{i=0}^{n-1} \in \mathbb{N}^n$ for its rank vector. Let $R_n = \{r_\sigma : \sigma \text{ a permutation of } \{0, \dots, n-1\}\} \subseteq \mathbb{N}^n$. The uniform rank law is the measure on $\mathbb{N}^n$

$$\mathrm{Rank}_n = \frac{1}{\# R_n} \sum_{r \in R_n} \delta_r,$$

the uniform distribution on the finite set $R_n$. Since $R_n$ is nonempty (it contains the rank vector $(1, \dots, n)$ of the identity), $\mathrm{Rank}_n$ is a probability measure for every $n$, including $n = 0$, where it is the point mass at the empty vector.

## Sources

- J. Hájek, Z. Šidák and P. K. Sen, *Theory of Rank Tests*, 2nd ed., Academic Press (1999).
