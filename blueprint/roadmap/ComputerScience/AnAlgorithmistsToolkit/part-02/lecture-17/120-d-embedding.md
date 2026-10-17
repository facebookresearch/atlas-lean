---
article_id: af_bcab69215c47ed9efd3d6dfb
declaration: structure
origin: cited
statement: formalized
lean: HighDimensional.IsDEmbedding
---

# Definition 4 (D-embedding)

Suppose that $X = \{x_1, x_2, \ldots, x_n\}$ is a finite set, $d$ is a metric on $X$, and $f: X \to \mathbb{R}^k$ is 1-Lipschitz, with $\|f(x_i) - f(x_j)\| \leq d(x_i, x_j)$. The ``distortion'' of $f$ is the minimum $D$ for which $\|f(x_i) - f(x_j)\| \leq d(x_i, x_j) \leq D\|f(x_i) - f(x_j)\|$ for some positive constant $\alpha$. We refer to $f$ as a $D$-embedding of $X$.

## Depends on

- [Definition 2 (c-Lipschitz)](116-c-lipschitz.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 17, Section 1.2](../../../../../sources/v1/AnAlgorithmistsToolkit.md)
