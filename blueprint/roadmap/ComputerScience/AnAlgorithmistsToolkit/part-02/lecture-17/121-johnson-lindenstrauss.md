---
article_id: af_d488bebf8beec7ce7a29b9ee
declaration: theorem
origin: cited
lean: HighDimensional.johnson_lindenstrauss
---

# Theorem 5 (Johnson-Lindenstrauss)

Let $X = \{x_1, x_2, \ldots, x_n\} \in \mathbb{R}^m$ (for any $m$) and let $k = O(\varepsilon^{-2} \log n)$. Let $\mathfrak{L} \subseteq \mathbb{R}^m$ be a uniform random $k$-dimensional subspace, $\{y_1, y_2, \ldots, y_n\}$ be projections of $x_i$ on $\mathfrak{L}$, and $y_i' = c y_i$ for some fixed constant $c = \Theta(k/m)$. Then, with high probability $\mathfrak{L}$ is a $(1+\varepsilon)$-embedding of $X$ into $\mathbb{R}^k$, i.e.\ for $x_i, x_j \in X$, $\|x_i - x_j\| \leq \|y_i' - y_j'\| \leq (1 + \varepsilon)\|x_i - x_j\|$.

## Depends on

- [Definition 4 (D-embedding)](120-d-embedding.md)

## Proof depends on

- [Lemma 3](119-lemma-3.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 17, Section 1.3](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
