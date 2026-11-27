# Bellman-Ford distances are realized by walks

Let $E$ be a list of integer-weighted
directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex. If Bellman-Ford run
on $E$ from $s$ returns distances $d$ and the distance $d(t)$ of a vertex $t$ is a finite integer
$\delta$, then there is a walk from $s$ to $t$ along edges of $E$ whose total weight is
$\delta$.
