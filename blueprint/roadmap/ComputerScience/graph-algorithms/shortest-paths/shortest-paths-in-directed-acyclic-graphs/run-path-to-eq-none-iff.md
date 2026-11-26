# Predecessor extraction fails exactly at infinite distances

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$, $s$ a source vertex, and
$\sigma$ a topological order of the directed graph with an edge $u \to v$ for each edge of $E$
from $u$ to $v$. After the one-pass relaxation of $E$ from $s$ in the order $\sigma$, for every
vertex $t$, following the predecessor edges back from $t$ fails to reach $s$ within $n$ steps if
and only if the computed distance to $t$ is infinite.
