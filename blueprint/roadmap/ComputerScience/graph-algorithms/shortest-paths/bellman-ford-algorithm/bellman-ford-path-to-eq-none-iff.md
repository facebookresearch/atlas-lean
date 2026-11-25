# Bellman-Ford path reconstruction fails exactly at infinite distances

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. If
Bellman-Ford run on $E$ from $s$ returns distances $d$, with $\infty$ marking a vertex that has
no finite distance, together with predecessor edges, then for every vertex $t$, reconstructing a
path to $t$ (following predecessor edges back from $t$ for at most $n$ steps until $s$ is
reached) fails if and only if $d(t) = \infty$.
