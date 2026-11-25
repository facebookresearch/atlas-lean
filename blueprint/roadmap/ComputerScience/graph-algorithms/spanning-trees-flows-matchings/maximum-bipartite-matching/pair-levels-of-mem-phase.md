# Levels of the pairs of a phase

In a bipartite graph with left vertices $0, \dots, a-1$, let
$\mu$ be a valid partner array (partners are neighbours, and no left vertex is the partner of two
right vertices), and let $d \le a$ be such that round $d + 1$ of the alternating layered search for
$\mu$ reaches an unmatched right vertex and no earlier round does. Then for every pair $(i, j)$ on
a path of the Hopcroft–Karp phase for $\mu$ there is $m \in \mathbb{N}$ such that $j$ is first
reached in round $m + 1$ and $i$ is among the left vertices reached within $m$ rounds.
