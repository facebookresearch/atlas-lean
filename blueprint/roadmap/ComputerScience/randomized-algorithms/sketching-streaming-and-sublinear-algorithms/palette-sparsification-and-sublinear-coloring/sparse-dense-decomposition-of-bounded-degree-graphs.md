# Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques

For $\varepsilon > 0$, a vertex $v$ of a graph $G$ with maximum degree $\Delta$ is *$\varepsilon$-sparse* if the subgraph induced by its neighborhood $N(v)$ has at most $(1 - \varepsilon)\binom{\Delta}{2}$ edges. There are absolute constants $\varepsilon_0, C > 0$ such that for every $0 < \varepsilon < \varepsilon_0$ every graph of maximum degree $\Delta$ admits a partition

$$
V = V^{\mathrm{sparse}} \sqcup K_1 \sqcup \dots \sqcup K_k
$$

such that every vertex of $V^{\mathrm{sparse}}$ is $\varepsilon$-sparse, and every *almost-clique* $K_i$ satisfies $(1 - C\varepsilon)\Delta \le |K_i| \le (1 + C\varepsilon)\Delta$, while every $v \in K_i$ has at most $C\varepsilon\Delta$ neighbors outside $K_i$ and at least $(1 - C\varepsilon)\Delta$ neighbors inside $K_i$.

## Proof sketch

Call an edge $\{u, v\}$ a *friend edge* if $|N(u) \cap N(v)| \ge (1 - \varepsilon)\Delta$, and a vertex *dense* if it has at least $(1 - \varepsilon)\Delta$ friends; a vertex that is not dense is $\Omega(\varepsilon)$-sparse by counting missing edges among its neighbors. The almost-cliques are the connected components of the friend graph on dense vertices; a transitivity-type estimate shows that friends of friends share most of their neighborhoods, which gives the size and boundary bounds after rescaling $\varepsilon$ by a constant.

## Sources

- David G. Harris, Johannes Schneider, Hsin-Hao Su, "Distributed (Delta+1)-Coloring in Sublogarithmic Rounds", STOC (2016); J. ACM 65 (2018).
- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886.
