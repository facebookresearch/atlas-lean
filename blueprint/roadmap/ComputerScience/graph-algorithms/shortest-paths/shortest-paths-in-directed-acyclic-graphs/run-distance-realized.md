# Finite DAG distances are path weights

Let $E$ be a list of integer-weighted edges on $n$
vertices, $s$ a source, and $\sigma$ a topological order of the directed graph obtained from $E$ by
forgetting weights. If the one-pass relaxation from $s$ in the order $\sigma$ gives a vertex $t$
the finite distance $d$, then there is a path from $s$ to $t$ made of edge occurrences of $E$
whose edge weights sum to $d$.
