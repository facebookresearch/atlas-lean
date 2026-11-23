# Greedy cut property of Kruskal's scan

Let $G$ be an input graph on the vertices
$\{0, \dots, n-1\}$, give each valid edge with weight $w$ and input ordinal $o$ the key
$(w, o)$, and compare keys lexicographically. The graph $G$ has the greedy cut property when
the following holds for every way of splitting the valid edges of $G$, sorted by key, into an
initial segment, an edge $e$ and a final segment. Let $P$ be the union-find partition obtained
by scanning the initial segment from the discrete parent forest with no accepted edges. If the
endpoints of $e$ lie in different classes of $P$, then the key of $e$ is at most the key of
every valid edge of $G$ whose endpoints lie in different classes of $P$.
