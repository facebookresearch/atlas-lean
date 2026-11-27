# Weighted path in an edge list

Let $E$ be a list of weighted directed edges on the vertices
$0, \dots, n-1$. A list $P = (e_1, \dots, e_k)$ of weighted directed edges is a weighted path in $E$
from $s$ to $t$ when every $e_i$ belongs to $E$, the target of $e_i$ is the source of $e_{i+1}$ for
every $i < k$, and either $k = 0$ and $s = t$, or $k \ge 1$, the source of $e_1$ is $s$ and the
target of $e_k$ is $t$.
