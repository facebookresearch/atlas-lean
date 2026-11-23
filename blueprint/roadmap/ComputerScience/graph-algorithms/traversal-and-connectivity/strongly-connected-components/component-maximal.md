# Each computed component is a full mutual-reachability class

Let $G$ be a directed graph,
let $B$ be one of the blocks returned by the strongly connected components algorithm on $G$, and
let $m$ be a vertex of $B$. Then for every vertex $v$ of $G$, the vertices $m$ and $v$ are strongly
connected (each is reachable from the other) if and only if $v$ lies in $B$.
