---
article_id: af_531bdae0f3057f47f5376cd1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ProbabilityTheory.deMoivreLaplace_clt
---

# Theorem (DeMoivre-Laplace limit theorem)

Let $X_i$ be i.i.d. random variables. Write $S_n = \sum_{i=1}^n X_i$. Suppose each $X_i$ is $1$ with probability $p$ and $0$ with probability $q = 1 - p$. Then $\lim_{n \to \infty} P\!\left\{a \leq \frac{S_n - np}{\sqrt{npq}} \leq b\right\} = \Phi(b) - \Phi(a)$, where $\Phi(b) - \Phi(a) = P\{a \leq Z \leq b\}$ when $Z$ is a standard normal random variable.

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.175 Theory of Probability (Spring 2014), Lecture 12, DeMoivre-Laplace limit theorem](../../../../../sources/v1/TheoryOfProbability.md)
