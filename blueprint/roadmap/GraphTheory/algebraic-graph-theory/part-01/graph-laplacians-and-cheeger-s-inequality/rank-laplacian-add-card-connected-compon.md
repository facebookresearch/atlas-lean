# Rank of the Laplacian plus number of components

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with no loops and with weights $w : E \to (0, \infty)$. Then

$$\operatorname{rank} L_w + c = \lvert V\rvert,$$

where $c$ is the number of connected components of the [underlying graph](../oriented-incidence-matrices/underlying-graph.md); equivalently the multiplicity of the eigenvalue $0$ of the [Laplacian](laplacian.md) is the number of components. This extends D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of 2 April 2025, Lemma 3.1.1, whose proof shows that for a connected graph the constants span the kernel.
