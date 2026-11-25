# A failed Kahn run leaves a directed cycle

Let $G$ be a finite directed graph. If
deterministic FIFO Kahn topological sorting of $G$ fails after processing the vertex list $P$
and leaving the vertex list $R$ unprocessed, then $G$ has a directed cycle in $R$: a nonempty
list of pairwise distinct vertices of $R$ in which each vertex has an edge to the next and the
last vertex has an edge to the first.
