# No path is shorter than the Floyd–Warshall distance

Let $w$ assign a weight in
$\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, suppose that
$w$ has no negative cycle, and let $D$ be the distance matrix computed by Floyd–Warshall from $w$.
Then for all vertices $s$ and $t$ and every weighted path $p$ from $s$ to $t$ (a nonempty vertex
sequence from $s$ to $t$ in which every consecutive pair has finite weight), $D(s, t)$ is at most
the weight of $p$, the sum of the weights of its consecutive pairs.
