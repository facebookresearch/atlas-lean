# Alternating path

Let $\mu$ be a partner array, giving each right vertex at most one left
vertex as its partner, let $k$ be a natural number and $j$ a right vertex. A list $P$ of pairs
$(i, j')$ of a left vertex $i$ and a right vertex $j'$ is an alternating path from $j$ within
round $k$ when all of the following hold: $P$ is nonempty and its first pair has right vertex
$j$; for every pair $(i, j')$ of $P$, $j'$ is a neighbour of $i$ but $i$ is not the partner of
$j'$; for every pair $(i, j')$ of $P$, the alternating search from the unmatched left vertices
reaches $i$ within $k$ rounds and $j'$ within $k + 1$ rounds; no left vertex and no right vertex
occurs twice in $P$; for any two consecutive pairs $(i, j')$ and $(i', j'')$ of $P$, $i$ is the
partner of $j''$; and the left vertex of the last pair of $P$ is the partner of no right vertex.

When $j$ is unmatched as well, $P$ is an augmenting path.
