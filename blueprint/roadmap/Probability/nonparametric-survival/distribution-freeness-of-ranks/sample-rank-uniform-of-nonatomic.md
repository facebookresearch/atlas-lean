# Ranks of a sample from an atomless law are uniform

Let $n \in \mathbb{N}$ and let $X_0, \dots, X_{n-1}$ be independent real random variables on a probability space $(\Omega, \mu)$, each with law $\nu$, a probability measure on $\mathbb{R}$ without atoms ($\nu(\{x\}) = 0$ for every $x \in \mathbb{R}$). The rank of $X_i$ in the sample is the competition rank $R_i = 1 + \#\{j : X_j < X_i\}$; tied observations would share the smallest rank of their group, but by the absence of atoms ties occur with probability $0$. For a permutation $\sigma$ of $\{0, \dots, n-1\}$ write $r_\sigma = (\sigma(i) + 1)_{i=0}^{n-1} \in \mathbb{N}^n$ for its rank vector. Let $\mathrm{Rank}_n = \frac{1}{\# R_n} \sum_{r \in R_n} \delta_r$ be the uniform rank law, the uniform distribution on the finite set $R_n = \{r_\sigma\} \subseteq \mathbb{N}^n$ of these rank vectors. Then the rank vector $R = (R_0, \dots, R_{n-1})$ has law $\mathrm{Rank}_n$:

$$\mu(R = r_\sigma) = \frac{1}{n!} \quad \text{for every permutation } \sigma, \qquad \mu(R \notin R_n) = 0,$$

whatever the atomless law $\nu$ is. Every ordering of the sample is equally likely.

## Sources

- J. Hájek, Z. Šidák and P. K. Sen, *Theory of Rank Tests*, 2nd ed., Academic Press (1999).
