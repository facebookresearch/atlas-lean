# Cost of the undirected Hierholzer algorithm

Let $E$ be a list of undirected edges and
$s$, $t$ vertices such that exactly $s$ and $t$ have odd degree in $E$ (no vertex has odd degree
when $s = t$), and suppose the first endpoint of every edge of $E$ is reachable from $s$ through
edges of $E$. Then the undirected Hierholzer algorithm on $E$ from $s$ costs exactly $|E|$, the
number of edges of $E$, in the cost model that charges one unit per removed edge.
