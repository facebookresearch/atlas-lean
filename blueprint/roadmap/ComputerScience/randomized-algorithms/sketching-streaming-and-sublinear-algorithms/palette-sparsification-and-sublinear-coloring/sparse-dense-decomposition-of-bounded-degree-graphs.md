# Sparse-dense decomposition of graphs of maximum degree Delta into sparse vertices and almost-cliques

Let $G = (V, E)$ be a graph with maximum degree $\Delta$ and let $\varepsilon \in [0, 1)$. An edge $\{u, v\}$ is an *$\varepsilon$-friend edge* if $|N(u) \cap N(v)| \ge (1 - \varepsilon)\Delta$; a vertex is *$\varepsilon$-dense* if it is incident to at least $(1 - \varepsilon)\Delta$ $\varepsilon$-friend edges, and *$\varepsilon$-sparse* otherwise. The neighborhood of every $\varepsilon$-sparse vertex spans at most $\binom{\Delta}{2} - \frac{1}{2}\varepsilon\Delta(\varepsilon\Delta - 1)$ edges, a nontrivial bound once $\varepsilon\Delta \ge 2$. The cruder bound $(1 - \varepsilon^2)\binom{\Delta}{2}$ fails for small $\varepsilon\Delta$: in a triangle with $\varepsilon = 0.1$ no edge is a friend edge, so every vertex is $\varepsilon$-sparse, yet its neighborhood spans $1 > 0.99\binom{2}{2}$ edges. For $0 \le \varepsilon < 1/10$, so that the Harris–Schneider–Su analysis applies to the parameter $2\varepsilon < 1/5$, every graph of maximum degree $\Delta$ admits a partition

$$
V = V^{\mathrm{sparse}}_{\star} \sqcup K_1 \sqcup \dots \sqcup K_k
$$

such that every vertex of $V^{\mathrm{sparse}}_{\star}$ is $\varepsilon$-sparse, every $2\varepsilon$-sparse vertex lies in $V^{\mathrm{sparse}}_{\star}$, and every *almost-clique* $K_i$ satisfies

1. $(1 - \varepsilon)\Delta \le |K_i| \le (1 + 6\varepsilon)\Delta$;
2. every $v \in K_i$ has at most $7\varepsilon\Delta$ neighbors outside $K_i$;
3. every $v \in K_i$ has at most $6\varepsilon\Delta$ non-neighbors inside $K_i$.

## Proof sketch

Pad the neighborhood of a vertex $v$ that is not $\varepsilon$-dense with isolated dummy vertices to exactly $\Delta$ vertices. Since $v$ has fewer than $(1 - \varepsilon)\Delta$ friend edges, more than $\varepsilon\Delta$ of the padded vertices are dummies or neighbors $u$ with $|N(u) \cap N(v)| < (1 - \varepsilon)\Delta$, and each of them is non-adjacent to more than $\varepsilon\Delta - 1$ of the other $\Delta - 1$ padded vertices; counting each missing pair at most twice gives at least $\frac{1}{2}\varepsilon\Delta(\varepsilon\Delta - 1)$ missing pairs when $\varepsilon\Delta \ge 1$, and the bound is trivial otherwise. For the partition, take the connected components of the graph of $2\varepsilon$-friend edges on the $2\varepsilon$-dense vertices; by the Harris–Schneider–Su analysis, valid since $2\varepsilon < 1/5$, every vertex of such a component has at most $6\varepsilon\Delta$ non-neighbors inside it. Keep as almost-cliques the components containing an $\varepsilon$-dense vertex $v$ and put all other vertices into $V^{\mathrm{sparse}}_{\star}$. The at least $(1 - \varepsilon)\Delta$ $\varepsilon$-friends of $v$ pairwise share $(1 - 2\varepsilon)\Delta$ neighbors, so they are $2\varepsilon$-dense and lie in the component of $v$, which gives the lower size bound; the upper size bound follows from the non-neighbor bound, and the outside-degree bound from the non-neighbor bound together with the lower size bound.

## Sources

- David G. Harris, Johannes Schneider, Hsin-Hao Su, "Distributed (Delta+1)-Coloring in Sublogarithmic Rounds", STOC (2016); J. ACM 65 (2018), Lemma 3.9 and Corollary 3.10 (for parameter below 1/5).
- Sepehr Assadi, Yu Chen, Sanjeev Khanna, "Sublinear Algorithms for (Delta + 1) Vertex Coloring", SODA (2019), arXiv:1807.08886, Lemma 2.3.
