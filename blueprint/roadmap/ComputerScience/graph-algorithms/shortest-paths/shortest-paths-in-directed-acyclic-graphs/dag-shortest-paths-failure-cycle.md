# A failed DAG shortest-path run exhibits a cycle

Let $E$ be a list of integer-weighted
directed edges on the vertices $\{0, \dots, n-1\}$ and $s$ a source vertex. If the DAG
shortest-path algorithm on $E$ from $s$ fails, reporting the processed vertices and the list $R$
of remaining vertices of its topological sort, then the directed graph with an edge $u \to v$ for
each edge of $E$ from $u$ to $v$ contains a nonempty directed cycle without repeated vertices
whose vertices all lie in $R$.
