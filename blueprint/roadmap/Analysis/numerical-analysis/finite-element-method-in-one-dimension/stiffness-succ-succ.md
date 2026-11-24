# Diagonal stiffness entry at an interior node

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$ with element lengths $h_i$. For
consecutive elements $i$ and $j = i + 1$, the [stiffness matrix](stiffness.md) satisfies
$K_{i+1, i+1} = 1/h_i + 1/h_j$ at their shared node $x_{i+1}$.
