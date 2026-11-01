---
article_id: af_5a40f7faf9300ae50be021d2
declaration: theorem
origin: cited
lean: BoundedDifferences.bounded_differences_inequality
---

# Theorem 9.1.1 (Bounded differences inequality)

Let $X_1 \in \Omega_1, \ldots, X_n \in \Omega_n$ be independent random variables. Suppose $f \colon \Omega_1 \times \cdots \times \Omega_n \to \mathbb{R}$ satisfies $|f(x_1, \ldots, x_n) - f(x'_1, \ldots, x'_n)| \leq 1$ whenever $(x_1, \ldots, x_n)$ and $(x'_1, \ldots, x'_n)$ differ on exactly one coordinate. Then the random variable $Z = f(X_1, \ldots, X_n)$ satisfies, for every $\lambda \geq 0$, $$\mathbb{P}(Z - \mathbb{E}Z \geq \lambda) \leq e^{-2\lambda^2/n} \quad \text{and} \quad \mathbb{P}(Z - \mathbb{E}Z \leq -\lambda) \leq e^{-2\lambda^2/n}.$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.1](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
