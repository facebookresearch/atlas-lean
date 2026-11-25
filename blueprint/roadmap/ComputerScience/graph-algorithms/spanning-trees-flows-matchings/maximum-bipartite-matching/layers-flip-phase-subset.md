# Distances do not decrease across a phase

Let the partner array of a bipartite graph with
$a$ left vertices be valid, and suppose that some round $r \le a + 1$ of the layered search
reaches an unmatched right vertex, so that a phase runs from the earliest such round. After
flipping all the paths that phase finds, for every $k \in \mathbb{N}$ the left vertices and the
right vertices reached within $k$ rounds of the layered search were already reached within $k$
rounds before the flip.

This is a step of Hopcroft and Karp's analysis.
