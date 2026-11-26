# Gomory-Hu trees

A **Gomory-Hu tree** (cut-equivalent tree) of a set function $f$ on $V$ is a spanning tree $T$ on $V$ such that for every tree edge $uv$, the vertex set of the component of $T - uv$ containing $u$ is a minimum $u$-$v$ cut of $f$. Weighting each tree edge $uv$ by $\lambda_f(u, v)$ gives the **weighted Gomory-Hu tree**.

## Depends on

- [Minimum s-t cuts of a set function](minimum-cuts-of-a-set-function.md)
- [Spanning tree](../../../../GraphTheory/algebraic-graph-theory/part-01/kirchhoff-s-matrix-tree-theorem/is-spanning-tree.md)

## Sources

- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
