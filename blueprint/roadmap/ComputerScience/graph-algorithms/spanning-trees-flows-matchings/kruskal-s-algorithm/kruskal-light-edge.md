# Kruskal accepts light edges

Let $G$ be a graph and let $e_1, \dots, e_m$ be its valid
edges sorted lexicographically by key (weight, then input ordinal). For a position $k$, let
$P_k$ be the partition of the vertices given by the union-find forest after Kruskal's scan,
started from the discrete forest, has processed $e_1, \dots, e_{k-1}$. If the endpoints of $e_k$
lie in different classes of $P_k$, then the weight of $e_k$ is at most the weight of every valid
edge of $G$ whose endpoints lie in different classes of $P_k$.
