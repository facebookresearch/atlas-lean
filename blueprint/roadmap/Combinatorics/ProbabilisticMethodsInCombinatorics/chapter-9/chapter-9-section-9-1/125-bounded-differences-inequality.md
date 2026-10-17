---
article_id: af_9b0c9ca65cf81f91d21aa1ea
declaration: theorem
origin: cited
lean: BoundedDifferences.bounded_differences_inequality
---

# Theorem 9.1.3 (Bounded differences inequality)

Let $X_1 \in \Omega_1, \ldots, X_n \in \Omega_n$ be independent random variables. Suppose $f \colon \Omega_1 \times \cdots \times \Omega_n \to \mathbb{R}$ satisfies $|f(x_1, \ldots, x_n) - f(x'_1, \ldots, x'_n)| \leq c_i$ whenever $(x_1, \ldots, x_n)$ and $(x'_1, \ldots, x'_n)$ differ only on the $i$-th coordinate. Here $c_1, \ldots, c_n$ are constants. Then the random variable $Z = f(X_1, \ldots, X_n)$ satisfies, for every $\lambda \geq 0$, $$\mathbb{P}(Z - \mathbb{E}Z \geq \lambda) \leq \exp\!\left(\frac{-2\lambda^2}{c_1^2 + \cdots + c_n^2}\right)$$ and $$\mathbb{P}(Z - \mathbb{E}Z \leq -\lambda) \leq \exp\!\left(\frac{-2\lambda^2}{c_1^2 + \cdots + c_n^2}\right).$$

## Depends on

This node has no prerequisites.

## Proof depends on

- [Theorem 9.2.9 (Azuma's inequality for Doob martingales)](../chapter-9-section-9-2/129-azuma-s-inequality-for-doob-martingales.md)

## Sources

- [MIT 18.226 Probabilistic Methods in Combinatorics (Fall 2022), Chapter 9, Section 9.1](../../../../../sources/v1/ProbabilisticMethodsInCombinatorics.md)
