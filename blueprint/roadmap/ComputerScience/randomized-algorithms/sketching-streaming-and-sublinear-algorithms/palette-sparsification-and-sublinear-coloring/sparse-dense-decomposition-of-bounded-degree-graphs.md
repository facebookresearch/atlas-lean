# Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques

Let $G = (V, E)$ be a graph with maximum degree $\Delta$ and let $\varepsilon \in [0, 1)$. An edge $\{u, v\}$ is an *$\varepsilon$-friend edge* if $|N(u) \cap N(v)| \ge (1 - \varepsilon)\Delta$; a vertex is *$\varepsilon$-dense* if it is incident to at least $(1 - \varepsilon)\Delta$ $\varepsilon$-friend edges, and *$\varepsilon$-sparse* otherwise. The neighborhood of every $\varepsilon$-sparse vertex spans at most $(1 - \varepsilon^2)\binom{\Delta}{2}$ edges. Every graph of maximum degree $\Delta$ admits a partition

$$
V = V^{\mathrm{sparse}}_{\star} \sqcup K_1 \sqcup \dots \sqcup K_k
$$

such that every vertex of $V^{\mathrm{sparse}}_{\star}$ is $\varepsilon$-sparse, every $2\varepsilon$-sparse vertex lies in $V^{\mathrm{sparse}}_{\star}$, and every *almost-clique* $K_i$ satisfies

1. $(1 - \varepsilon)\Delta \le |K_i| \le (1 + 6\varepsilon)\Delta$;
2. every $v \in K_i$ has at most $7\varepsilon\Delta$ neighbors outside $K_i$;
3. every $v \in K_i$ has at most $6\varepsilon\Delta$ non-neighbors inside $K_i$.

## Proof sketch

A vertex that is not $\varepsilon$-dense has at least $\varepsilon\Delta$ neighbors sharing at most $(1 - \varepsilon)\Delta$ neighbors with it, each missing $\varepsilon\Delta$ edges inside the neighborhood, which gives the edge bound after padding the neighborhood to $\Delta$ vertices. For the partition, take the connected components of the graph of $2\varepsilon$-friend edges on the $2\varepsilon$-dense vertices; by the Harris–Schneider–Su analysis every vertex of such a component has at most $6\varepsilon\Delta$ non-neighbors inside it. Keep as almost-cliques the components containing an $\varepsilon$-dense vertex $v$ and put all other vertices into $V^{\mathrm{sparse}}_{\star}$. The at least $(1 - \varepsilon)\Delta$ $\varepsilon$-friends of $v$ pairwise share $(1 - 2\varepsilon)\Delta$ neighbors, so they are $2\varepsilon$-dense and lie in the component of $v$, which gives the lower size bound; the upper size bound follows from the non-neighbor bound, and the outside-degree bound from the non-neighbor bound together with the lower size bound.

## Sources

- David G. Harris, Johannes Schneider, Hsin-Hao Su, "Distributed (Delta+1)-Coloring in Sublogarithmic Rounds", STOC (2016); J. ACM 65 (2018).
- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
