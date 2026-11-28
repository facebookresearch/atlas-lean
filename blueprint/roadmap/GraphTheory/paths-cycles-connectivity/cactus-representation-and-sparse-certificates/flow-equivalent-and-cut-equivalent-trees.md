# Flow-equivalent and cut-equivalent trees of weighted graphs

Let $G = (V, E, w)$ be a connected undirected graph with positive weights and let $\lambda_G(s,t)$ denote its minimum $s$-$t$ cut value. A tree $T = (V, E_T, c)$ on the same vertex set with positive edge weights $c$ is *flow-equivalent* to $G$ if for all distinct $s, t \in V$

$$
\lambda_G(s, t) = \min_{e \in P_T(s,t)} c(e),
$$

where $P_T(s,t)$ is the path from $s$ to $t$ in $T$. It is *cut-equivalent* (a cut tree) if in addition, for all $s \ne t$ and every minimum-weight edge $e$ on $P_T(s,t)$, the vertex set $S$ of the component of $T - e$ containing $s$ is a minimum $s$-$t$ cut of $G$, i.e. $w(\partial_G S) = c(e)$. For $\varepsilon > 0$, a tree $T = (V, E_T, c)$ is a *$(1+\varepsilon)$-approximate cut-equivalent tree* if for all $s \ne t$ and every minimum-weight edge $e$ on $P_T(s,t)$, the vertex set $S$ of the component of $T - e$ containing $s$ has cut capacity equal to the weight of $e$, $w(\partial_G S) = c(e)$, and satisfies $\lambda_G(s,t) \le w(\partial_G S) \le (1+\varepsilon)\lambda_G(s,t)$; without the condition $w(\partial_G S) = c(e)$ the tree weights would be unconstrained. The *all-pairs max-flow problem* asks for a cut-equivalent tree. Cut-equivalent trees of the cut function of $G$ are exactly its weighted Gomory-Hu trees.

## Depends on

- [Edge cuts separating two vertices](../menger-s-theorem/is-stedge-cut.md)
- [Gomory-Hu trees](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/gomory-hu-trees/gomory-hu-tree.md)

## Sources

- Ralph E. Gomory, Te C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics (1961).
- Amir Abboud, Robert Krauthgamer, Ohad Trabelsi, "Cut-Equivalent Trees are Optimal for Min-Cut Queries", FOCS (2020), arXiv:2009.06090.
- Jason Li, Debmalya Panigrahi, "Approximate Gomory-Hu Tree Is Faster Than n-1 Max-Flows", STOC (2021), arXiv:2111.02022.
