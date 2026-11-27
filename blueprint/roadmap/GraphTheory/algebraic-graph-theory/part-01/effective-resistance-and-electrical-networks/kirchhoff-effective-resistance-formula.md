# Kirchhoff's effective resistance formula

Let $G$ be a finite connected simple graph. For every edge $uv$ of $G$, the fraction of spanning trees of $G$ that contain $uv$ equals the effective resistance between $u$ and $v$ with unit conductances:

$$\frac{\#\{T \text{ spanning tree of } G : uv \in T\}}{\#\{T \text{ spanning tree of } G\}} = R_{\mathrm{eff}}(u, v),$$

that is, $\mathbb{P}[uv \in T] = R_{\mathrm{eff}}(u, v)$ for a uniform spanning tree $T$ (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 4.2, Kirchhoff's Effective Resistance Formula, with $c \equiv 1$). The [effective resistance](effective-resistance.md) is that of the multigraph of darts of $G$ with conductance $1/2$ on each dart, whose Laplacian is the Laplacian of $G$, so that each edge of $G$ is one unit resistor.

This is the unit-conductance case of the source's formula; the weighted formula is [Kirchhoff's effective resistance formula, weighted](kirchhoff-effective-resistance-formula-weighted.md). Lyons and Peres prove $\mathbb{P}[e \in T] = c(e) R(e^- \leftrightarrow e^+)$ with Wilson's algorithm (Theorem 4.1) and the interpretation of current as expected net crossings (Proposition 2.2). Exercise 4.16 of the source derives the [matrix-tree theorem](../kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md) from this formula, and conversely the formula follows from the matrix-tree theorem by counting the spanning trees that contain $e$ as the spanning trees of the contraction $G/e$. For a tree, every edge lies in the only spanning tree and has effective resistance $1$.

## Background

- [Kirchhoff's matrix-tree theorem](../kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md): the number of spanning trees of $G$ in the denominator, as a determinant.
- [Foster's identity](sum-mul-effective-resistance.md): summing this formula over the edges recovers $\sum_e R_{\mathrm{eff}}(e) = n - 1$, the number of edges of a spanning tree.
