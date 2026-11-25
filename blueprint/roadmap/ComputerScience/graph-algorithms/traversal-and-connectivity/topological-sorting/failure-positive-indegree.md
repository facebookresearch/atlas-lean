# Unprocessed vertices of a failed Kahn run have positive indegree among the unprocessed

Let $G$ be a finite directed graph. If deterministic FIFO Kahn topological sorting of $G$ fails
after processing the vertex list $P$ and leaving the vertex list $R$ unprocessed, then for every
vertex $v$ in $R$ the indegree of $v$ within $R$, the number of entries $u$ of $R$ such that $G$
has an edge from $u$ to $v$, is positive.
