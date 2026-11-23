# Laplacian quadratic form

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with weights $w : E \to \mathbb{R}$ and [Laplacian](laplacian.md) $L$. For every $x : V \to \mathbb{R}$,

$$x^{\mathsf T} L x = \sum_{e \in E} w_e \big(x(e^-) - x(e^+)\big)^2$$

(D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, equation (3.1)).
