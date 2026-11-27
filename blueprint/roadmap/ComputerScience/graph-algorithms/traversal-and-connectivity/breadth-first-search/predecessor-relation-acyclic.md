# The saved-parent relation is acyclic

Let $G$ be a finite directed graph given by
adjacency lists and let $s$ and $v$ be vertices. In the breadth-first search forest of $G$ from
$s$, there is no sequence $v = x_0, x_1, \dots, x_k = v$ with $k \ge 1$ in which each $x_i$ is
the saved parent of $x_{i+1}$.
