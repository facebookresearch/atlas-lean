# Phase paths are disjoint augmenting paths

Let $\mathrm{mate}$ be a valid partner
assignment, $k$ a level, $J$ a list of right vertices each unmatched and reached within $k + 1$
rounds of the alternating layered search, and $U_L$, $U_R$ sets of left and right vertices. Then
every path that the phase search at level $k$ collects from $J$ with used left vertices $U_L$ and
used right vertices $U_R$ is an augmenting path from some right vertex, with left vertices reached
within $k$ rounds and right vertices within $k + 1$ rounds; no left vertex and no right vertex
occurs twice among all pairs of all these paths; and every pair $(i, j)$ of these paths has
$i \notin U_L$ and $j \notin U_R$.
