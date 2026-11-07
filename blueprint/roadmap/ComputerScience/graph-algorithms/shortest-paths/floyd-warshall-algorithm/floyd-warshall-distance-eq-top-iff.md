# Floyd–Warshall reports $\infty$ exactly for unreachable pairs

Let $w$ assign a weight
in $\mathbb{Z} \cup \{\infty\}$ to each ordered pair of vertices in $\{0, \dots, n-1\}$, and let $D$
be the distance matrix computed by Floyd–Warshall from $w$. For all vertices $s$ and $t$,
$D(s, t) = \infty$ if and only if there is no weighted path from $s$ to $t$, that is, no nonempty
vertex sequence from $s$ to $t$ in which every consecutive pair has finite weight.
