# Connected components computes reachability

Let $n$ be a natural number and let $E$ be a
list of pairs of vertices in $\{0, \dots, n-1\}$. For all vertices $a, b < n$, $a$ and $b$ are
equivalent in the union-find structure returned by CONNECTED-COMPONENTS on $n$ and $E$ if and
only if $a$ and $b$ are joined by a path in the simple graph on $\{0, \dots, n-1\}$ whose edges
are the unordered pairs $\{u, v\}$ with $(u, v)$ in $E$ and $u \ne v$.
