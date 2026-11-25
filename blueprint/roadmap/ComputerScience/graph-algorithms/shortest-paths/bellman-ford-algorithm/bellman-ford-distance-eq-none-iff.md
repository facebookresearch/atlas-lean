# Bellman-Ford leaves exactly the unreachable vertices at infinite distance

Let $E$ be a
list of integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a
vertex. If Bellman-Ford run on $E$ from $s$ returns distances $d$, with $\infty$ marking a vertex
that has no finite distance, then for every vertex $t$, $d(t) = \infty$ if and only if $t$ is not
reachable from $s$ in the directed graph obtained from $E$ by forgetting the weights.
