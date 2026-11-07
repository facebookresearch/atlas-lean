# Infinite DAG distances are exactly unreachable vertices

Let $E$ be a list of
integer-weighted edges on $n$ vertices, $s$ a source, and $\sigma$ a topological order of the
directed graph $G$ obtained from $E$ by forgetting weights. For every vertex $t$, the one-pass
relaxation from $s$ in the order $\sigma$ leaves the distance of $t$ infinite if and only if $t$ is
not reachable from $s$ in $G$.
