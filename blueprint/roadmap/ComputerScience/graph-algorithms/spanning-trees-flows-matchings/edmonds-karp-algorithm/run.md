# Augmenting-path iteration with fuel

Let $c$ be a capacity matrix with natural-number
entries on the vertices $\{0, \dots, n - 1\}$, let $s$ be a source and $t$ a sink, let $k$ be a fuel
bound and let $f$ be a flow (an integer-valued matrix on pairs of vertices). The iteration returns
$f$ if $k = 0$ or $s = t$. Otherwise it runs the breadth-first shortest-path search from $s$ to $t$
in the residual graph of $f$ with respect to $c$. If the search finds no path, the iteration returns
$f$. If it returns a path $P$, let $b$ be the bottleneck of $P$, the least residual capacity
$c(u, v) - f(u, v)$ over the edges $(u, v)$ of $P$; the iteration augments $f$ along $P$ by $b$,
adding $b$ to $f(u, v)$ and subtracting $b$ from $f(v, u)$ for each edge $(u, v)$ of $P$, and
continues from the augmented flow with fuel $k - 1$.
