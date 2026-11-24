# The Laplacian of a multigraph applied to a potential

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with conductances $w : E \to \mathbb{R}$ and [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) $L$. For every $h : V \to \mathbb{R}$ and every $x \in V$,

$$(L h)(x) = \pi(x)\, h(x) - N(x),$$

where $\pi(x) = \sum_e w_e([e^- = x] + [e^+ = x])$ is the [weighted degree](../../part-02/conductance-and-cheeger-s-inequality/weighted-degree.md) and $N(x)$ the [neighbour sum](neighbour-sum.md); that is, $L = D - A$ for the weighted degree $D$ and the weighted adjacency $A$ (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Exercise 2.62, the network Laplacian $\Delta_G$). A loop $e$ at $x$ contributes $2 w_e h(x)$ to both terms, and the two contributions cancel.
