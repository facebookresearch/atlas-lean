# Kruskal's greedy cut property

Let $G$ be a graph and let $e_1, \dots, e_m$ be its valid
edges sorted lexicographically by key (weight, then input ordinal). For a position $k$, let
$P_k$ be the partition of the vertices given by the union-find forest after Kruskal's scan,
started from the discrete forest, has processed $e_1, \dots, e_{k-1}$. If the endpoints of $e_k$
lie in different classes of $P_k$, then for every valid edge $c$ of $G$ whose endpoints lie in
different classes of $P_k$, the key of $e_k$ is lexicographically at most the key of $c$: either
$e_k$ has smaller weight than $c$, or the same weight and input ordinal at most that of $c$.
