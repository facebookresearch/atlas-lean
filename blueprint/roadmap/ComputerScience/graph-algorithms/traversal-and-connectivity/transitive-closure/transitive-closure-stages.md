# Staged transitive-closure computation

Let $A$ be a Boolean adjacency matrix on the
vertices $0, \dots, n-1$ and let $k \le n$. The computation first builds the $n \times n$ Boolean
matrix $T^{(0)}$ whose entry $(i, j)$ is true exactly when $i = j$ or $A_{ij}$ is true. Then, for
$p = 0, \dots, k - 1$, it builds a new matrix $T^{(p+1)}$ from the saved matrix $T^{(p)}$ by
$T^{(p+1)}_{ij} = T^{(p)}_{ij} \lor (T^{(p)}_{ip} \land T^{(p)}_{pj})$, and it returns $T^{(k)}$.
One time unit is charged for each cell assignment.
