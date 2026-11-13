# Stage-$k$ shortest-path weight

Let $w$ assign to each ordered pair of vertices in
$\{0, \dots, n-1\}$ a weight in $\mathbb{Z} \cup \{\infty\}$, let $k$ be a natural number, let
$s$ and $t$ be vertices and let $d \in \mathbb{Z} \cup \{\infty\}$. A weighted path from $s$ to
$t$ is a nonempty list of vertices that starts at $s$, ends at $t$ and has $w(u, v) \ne \infty$
for every pair of consecutive vertices $u, v$; its weight is the sum of these values $w(u, v)$,
and its intermediate vertices are all its entries except the first and the last. Then $d$ is the
stage-$k$ shortest-path weight from $s$ to $t$ when $d$ is at most the weight of every weighted
path from $s$ to $t$ whose intermediate vertices are all less than $k$, and either $d = \infty$ or
some such path has weight exactly $d$.
