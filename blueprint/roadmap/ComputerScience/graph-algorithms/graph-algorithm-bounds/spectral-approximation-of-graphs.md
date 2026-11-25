# Spectral approximation of graphs

Let $G$ and $H$ be graphs on the same vertex set $V$ with nonnegative edge weights and Laplacians $L_G$ and $L_H$, and $\varepsilon \in (0, 1)$. $H$ is an $\varepsilon$-*spectral approximation* of $G$ if $(1 - \varepsilon)\, x^{\mathsf T} L_G x \le x^{\mathsf T} L_H x \le (1 + \varepsilon)\, x^{\mathsf T} L_G x$ for all $x \in \mathbb{R}^V$, and an $\varepsilon$-*cut approximation* if this holds for all $x \in \{0,1\}^V$, that is, every cut has weight within a factor $1 \pm \varepsilon$. Every spectral approximation is a cut approximation.

## Depends on

- [Laplacian quadratic form](../../../GraphTheory/algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/dot-product-mul-vec-laplacian.md)

## Sources

- D. A. Spielman and N. Srivastava, "Graph sparsification by effective resistances", *SIAM Journal on Computing* 40(6):1913–1926, 2011
