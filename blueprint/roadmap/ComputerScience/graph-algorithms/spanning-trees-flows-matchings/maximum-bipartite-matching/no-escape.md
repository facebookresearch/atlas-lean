# No shortest escape

Let $\mu$ be a partner array, $U$ a set of left vertices, $D$ a set of
right vertices and $z$ a right vertex. Then $z$ has no escape avoiding $U$ and $D$ when there are
no $m \in \mathbb{N}$ and no list of pairs $(i_1, j_1), \dots, (i_{m+1}, j_{m+1})$ such that $z$ is
first reached in round $m + 1$ of the alternating layered search for $\mu$, the list is an
alternating chain from $z$, no $i_t$ lies in $U$, and no $j_t$ with $t \ge 2$ lies in $D$. Here
the list is an alternating chain from $z$ when $j_1 = z$, each $j_t$ is adjacent to $i_t$ with
$\mu(j_t) \ne i_t$, $\mu(j_{t+1}) = i_t$ for $t \le m$, and $i_{m+1}$ is unmatched.

A phase gives this property to every right vertex it marks dead after a failed search.
