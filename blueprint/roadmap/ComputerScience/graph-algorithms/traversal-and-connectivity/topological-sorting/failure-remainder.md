# A failed Kahn run splits the vertices into processed and unprocessed ones

Let $G$ be a
finite directed graph. If deterministic FIFO Kahn topological sorting of $G$ fails after
processing the vertex list $P$ and leaving the vertex list $R$ unprocessed, then $R$ is nonempty,
neither $P$ nor $R$ has repeated entries, a vertex lies in the vertex list of $G$ if and only if
it lies in $P$ or in $R$, and no vertex lies in both $P$ and $R$.
