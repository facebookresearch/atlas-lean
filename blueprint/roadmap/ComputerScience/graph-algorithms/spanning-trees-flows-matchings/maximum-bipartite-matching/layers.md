# Alternating breadth-first layers

Let $\mu$ give each right vertex $j$ of a bipartite
graph at most one partner $\mu(j)$ among the left vertices. The layers are pairs $(Z_k, R_k)$ of a
set $Z_k$ of left vertices and a set $R_k$ of right vertices, defined by recursion on $k$: $Z_0$ is
the set of unmatched left vertices (those that are the partner of no right vertex) and
$R_0 = \emptyset$; $R_{k+1}$ is the set of right vertices $j$ adjacent to some $i \in Z_k$ with
$\mu(j) \ne i$, and $Z_{k+1}$ is $Z_k$ together with the left vertices $\mu(j)$ for $j \in R_{k+1}$.

The layers are cumulative on both sides: $Z_k$ holds the left vertices reached within $k$ rounds
and $R_k$ the right vertices reached within $k$ rounds. The round where a vertex is first reached
is its breadth-first level.
