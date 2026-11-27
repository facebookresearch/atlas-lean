# Spectral expanders have edge expansion, through Cheeger's inequality

Let $G$ be a finite simple graph on $N$ vertices with adjacency matrix $A$, and let $d$ be a natural number and $\lambda$ a real number such that $G$ is a [spectral expander](is-spectral-expander.md) of degree $d$ with parameter $\lambda$: $G$ is $d$-regular, $\lambda \ge 0$ and $\lVert A x\rVert \le d \lambda \lVert x\rVert$ for every $x$ orthogonal to the constant vector. For every vertex set $S$,

$$d(1 - \lambda)\, \lvert S\rvert\, \lvert V \setminus S\rvert \le N \cdot \tfrac12 \#\{\text{darts } (a, b) \text{ with exactly one of } a, b \text{ in } S\},$$

and the right side is $N$ times the number of edges of $G$ leaving $S$: the cut weight of $S$ in the multigraph of darts of $G$ with weights $1/2$. This applies the [easy direction of Cheeger's inequality](../../algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/mul-card-mul-card-compl-le-of-forall.md) (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Theorem 20.1.1) with the [Laplacian Rayleigh quotient bound](laplacian-rayleigh-quotient.md).

## Background

- [Easy direction of Cheeger's inequality](../../algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/mul-card-mul-card-compl-le-of-forall.md): the
  theorem applied, with the Laplacian Rayleigh bound as its hypothesis.
- [Spectral expanders have edge expansion, from the mixing lemma](spectral-edge-expansion.md): the
  same bound obtained from the expander mixing lemma, with the edge count $e(S, V \setminus S)$.
