# The DAG shortest-path algorithm succeeds exactly on acyclic graphs

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and $s$ a source vertex. The
DAG shortest-path algorithm on $E$ from $s$ succeeds if and only if the directed graph with an
edge $u \to v$ for each edge of $E$ from $u$ to $v$ has no directed cycle.

This includes disconnected graphs: a cycle unreachable from $s$ still causes failure.
