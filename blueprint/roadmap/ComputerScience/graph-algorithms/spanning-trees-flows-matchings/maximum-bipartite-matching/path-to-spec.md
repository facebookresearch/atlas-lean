# The walk back is an alternating path

Let $\mathrm{mate}$ be a valid partner assignment.
For every level $k$ and every right vertex $j$ reached within $k + 1$ rounds of the alternating
layered search, the walk back from $j$ at level $k$ is an alternating path from $j$ at level $k$:
it starts at $j$, its pairs are non-matching edges, its left vertices are reached within $k$
rounds and its right vertices within $k + 1$ rounds, no vertex occurs twice, each right vertex
after the first is the partner of the previous left vertex, and the last left vertex is
unmatched.
