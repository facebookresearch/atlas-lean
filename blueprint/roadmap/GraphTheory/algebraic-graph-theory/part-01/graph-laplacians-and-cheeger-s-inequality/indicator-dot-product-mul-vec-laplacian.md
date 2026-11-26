# Quadratic form of an indicator is the cut weight

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to \mathbb{R}$ and [Laplacian](laplacian.md) $L$. For every $S \subseteq V$, with $1_S$ the [indicator vector](indicator.md) of $S$,

$$1_S^{\mathsf T} L\, 1_S = \sum_{e \in \partial S} w_e,$$

the total weight of the [cut](../../../graph-families-and-operations/finite-multigraphs/cut.md) $\partial S$ of $S$, the edges with exactly one endpoint in $S$ (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, proof of Theorem 20.1.1).
