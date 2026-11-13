# Floyd–Warshall computes shortest-path distances

Let $w$ assign a weight in
$\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, suppose that
$w$ has no negative cycle, and let $D$ be the distance matrix computed by Floyd–Warshall from $w$.
Then for all vertices $s$ and $t$, $D(s, t)$ is at most the weight of every weighted path from $s$
to $t$, and either $D(s, t) = \infty$ or $D(s, t)$ is the weight of some weighted path from $s$ to
$t$. Here a weighted path is a nonempty vertex sequence in which every consecutive pair has finite
weight, and its weight is the sum of these weights.

Formally this is the stage-$n$ characterization, which considers only paths whose intermediate
vertices are all below $n$; every path qualifies.
