# Finite Floyd–Warshall distances are attained

Let $w$ assign a weight in
$\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, and let $D$
be the distance matrix computed by Floyd–Warshall from $w$. If $D(s, t) = d$ for vertices $s$, $t$
and an integer $d$, then there is a weighted path from $s$ to $t$ (a nonempty vertex sequence from
$s$ to $t$ in which every consecutive pair has finite weight) whose weight, the sum of the weights
of its consecutive pairs, is $d$.
