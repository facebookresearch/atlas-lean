# Augmenting paths have positive bottleneck

Let $c$ be a capacity matrix with
natural-number entries and $f$ any integer matrix (the flow) on the vertices $0, \dots, n - 1$,
and let $s \ne t$ be vertices. If $p$ is a duplicate-free path from $s$ to $t$ in the residual
graph of $c$ and $f$, then the bottleneck of $p$, the minimum of $c(u, v) - f(u, v)$ over
consecutive vertices $u, v$ of $p$, is positive.
