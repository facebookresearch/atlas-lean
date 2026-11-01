---
article_id: af_39b8696d10ac49d5352fefaa
declaration: theorem
origin: cited
lean: GaussianLinearTransform.concrete_converse_covariance_entries
---

# Lemma 1 (Chapter 1 (Brownian Motion))

Let $X = (X_1, \ldots, X_m)$ be independent Gaussian random variables with mean zero. Let $A = (a_{ik})$ be an invertible (real-valued) matrix and define $Y = (Y_1, \ldots, Y_m)$ by $Y_j = \sum_{k=1}^m a_{jk} X_k$. Then for every $a = (a_1, \ldots, a_m) \in \mathbb{R}^m$, $a \cdot Y = \sum_{j=1}^{m} a_j Y_j$ is a Gaussian random variable with mean $0$. Conversely, if $Z = (Z_1, \ldots, Z_m)$ are random variables such that for every $a = (a_1, \ldots, a_m)$, $a \cdot Z = \sum_{j=1}^{m} a_j Z_j$ is a Gaussian random variable with mean $0$ and covariances coincide with those of $Y$, $\mathbb{E}(Z_i Z_k) = \mathbb{E}(Y_i Y_k)$, then the joint distribution of $Z = (Z_1, \ldots, Z_m)$ is the same as that of $Y$. In other words, $P(Z \in E) = P(Y \in E)$ for all Borel sets $E \subset \mathbb{R}^m$. Moreover, $A^{-1}Z$ has the same probability distribution as $X$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Proposition 1 (Chapter 1 (Brownian Motion))](032-proposition-1.md)

## Sources

- [MIT 18.103 Fourier Analysis (Fall 2013), Chapter 1 (Brownian Motion)](../../../../sources/v1/FourierAnalysis.md)
