# One augmenting-path step

Let $c$ be a capacity matrix with natural-number entries on the
vertices $\{0, \dots, n - 1\}$, let $s$ be a source and $t$ a sink, and let $f$ be a flow (an
integer-valued matrix on pairs of vertices). Run the breadth-first shortest-path search from $s$ to
$t$ in the residual graph of $f$ with respect to $c$. If it finds no path, the step returns $f$. If
it returns a path $P$, let $b$ be the bottleneck of $P$, the least residual capacity
$c(u, v) - f(u, v)$ over the edges $(u, v)$ of $P$ (and $b = 0$ if $P$ has no edges); the step
returns $f$ augmented along $P$ by $b$, that is, $b$ is added to $f(u, v)$ and subtracted from
$f(v, u)$ for each edge $(u, v)$ of $P$.
