# Bellman-Ford distances are lower bounds on walk weights

Let $E$ be a list of
integer-weighted directed edges on the vertices $\{0, \dots, n-1\}$ and let $s$ be a vertex.
If Bellman-Ford run on $E$ from $s$ returns distances $d$, the distance $d(t)$ of a vertex $t$
is a finite integer $\delta$, and $P$ is a walk from $s$ to $t$ along edges of $E$ (vertices may
repeat), then $\delta$ is at most the total weight of $P$.
