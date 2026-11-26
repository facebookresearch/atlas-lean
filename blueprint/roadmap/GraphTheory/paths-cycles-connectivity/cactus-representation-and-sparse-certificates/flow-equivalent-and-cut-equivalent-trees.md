# Flow-equivalent and cut-equivalent trees of weighted graphs

Let $G = (V, E, w)$ be a connected undirected graph with positive weights and let $\lambda_G(s,t)$ denote its minimum $s$-$t$ cut value. A tree $T = (V, E_T, c)$ on the same vertex set with positive edge weights $c$ is *flow-equivalent* to $G$ if for all distinct $s, t \in V$

$$
\lambda_G(s, t) = \min_{e \in P_T(s,t)} c(e),
$$

where $P_T(s,t)$ is the path from $s$ to $t$ in $T$. It is *cut-equivalent* (a cut tree) if in addition, for all $s \ne t$ and every minimum-weight edge $e$ on $P_T(s,t)$, the vertex set $S$ of the component of $T - e$ containing $s$ is a minimum $s$-$t$ cut of $G$, i.e. $w(\partial_G S) = c(e)$. For $\varepsilon > 0$, a tree is a *$(1+\varepsilon)$-approximate cut-equivalent tree* if each such $S$ satisfies $\lambda_G(s,t) \le w(\partial_G S) \le (1+\varepsilon)\lambda_G(s,t)$. The *all-pairs max-flow problem* asks for a cut-equivalent tree.

## Depends on

- [Max-flow min-cut theorem](../../matchings-and-flows/max-flow-min-cut-theorem/max-flow-min-cut.md)
- [Edge cuts separating two vertices](../menger-s-theorem/is-stedge-cut.md)
- [Spanning tree](../../algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)

## Sources

- Ralph E. Gomory, Te C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics (1961).
- Amir Abboud, Robert Krauthgamer, Ohad Trabelsi, "Cut-Equivalent Trees are Optimal for Min-Cut Queries", FOCS (2020), arXiv:2009.06090.
