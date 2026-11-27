# Partner arrays that describe a matching

Consider a bipartite graph with left vertices
$\{0, \dots, a-1\}$, right vertices $\{0, \dots, b-1\}$ and, for each left vertex $i$, a list of
its neighbours. A partner array assigns to each right vertex $j$ either no partner or a left
vertex as its partner. It is valid when every partner is a neighbour (if $i$ is the partner of
$j$, then $j$ is in the list of neighbours of $i$) and no left vertex is the partner of two
different right vertices (if $i$ is the partner of both $j$ and $j'$, then $j = j'$).
