# Finite DAG distances are at most every path weight

Let $E$ be a list of integer-weighted
edges on $n$ vertices, $s$ a source, and $\sigma$ a topological order of the directed graph
obtained from $E$ by forgetting weights. If the one-pass relaxation from $s$ in the order $\sigma$
gives a vertex $t$ the finite distance $d$, then $d \le w(p)$ for every path $p$ from $s$ to $t$
made of edge occurrences of $E$, where $w(p)$ is the sum of the weights of the edges of $p$.
