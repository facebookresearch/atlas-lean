---
article_id: af_0fd4b420ae6c5901cd3c36c3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: SpectraCommonGraphs.ringGraph_lapMatrix_eigenvectors
---

# Lemma 16 (Ring graph)

The Laplacian for the ring graph $R_n$ on $n$ vertices has eigenvectors $x_k(u) = \sin(2\pi k u / n)$ and $y_k(u) = \cos(2\pi k u / n)$ for $0 \leq k \leq n/2$. Both $x_k$ and $y_k$ have eigenvalue $2 - 2\cos(2\pi k / n)$. Note that $x_0 = 0$ should be ignored and $y_0 = \mathbf{1}$, and when $n$ is even $x_{n/2} = 0$ should be ignored and we only have $y_{n/2}$.

## Depends on

- [Definition 1 (Lecture 1, Section 2)](../../lecture-1/001-definition-1.md)

## Sources

- [MIT 18.409 An Algorithmist's Toolkit (Fall 2009), Lecture 2, Section 4](../../../../../../sources/v1/AnAlgorithmistsToolkit.md)
