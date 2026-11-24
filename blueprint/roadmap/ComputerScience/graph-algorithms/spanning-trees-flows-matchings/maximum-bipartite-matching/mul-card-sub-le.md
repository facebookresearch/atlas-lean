# The deficit is at most $b / d$

In a bipartite graph with right vertices $0, \dots, b-1$,
let $\mu$ be a valid partner array (partners are neighbours, and no left vertex is the partner of
two right vertices), let $M$ be any matching of the graph, and let $d \in \mathbb{N}$. Suppose that
for every $k < d$, no unmatched right vertex is among the right vertices reached within $k + 1$
rounds of the alternating layered search for $\mu$. Then $d \cdot \max(|M| - |P_\mu|, 0) \le |R_d|$,
where $P_\mu$ is the set of pairs $(i, j)$ with $\mu(j) = i$ and $R_d$ is the set of right vertices
reached within $d$ rounds.

This is the counting step of Hopcroft and Karp's bound: since $R_d$ has at most $b$ elements, the
deficit of the current matching against any matching is at most $b / d$ when $d \ge 1$.
