# Kernel of the Laplacian

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops, with weights $w : E \to (0, \infty)$ and [Laplacian](laplacian.md) $L$. A vector $x : V \to \mathbb{R}$ satisfies $L x = 0$ if and only if $x(u) = x(v)$ whenever $u$ and $v$ lie in the same connected component of the [underlying graph](../oriented-incidence-matrices/underlying-graph.md) (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, proof of Lemma 3.1.1).
