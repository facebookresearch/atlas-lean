# Every symmetric submodular function has a Gomory-Hu tree

Every symmetric submodular set function $f$ on a nonempty finite set $V$ has a Gomory-Hu tree. In particular, every undirected graph with nonnegative edge weights (in a linearly ordered field) has a Gomory-Hu tree for its cut function.

## Proof sketch

Gomory and Hu's recursion: pick $s, t$ in a current super-node, take a minimum $s$-$t$ cut, and split the super-node; uncrossing shows the cut can be chosen compatible with the cuts already used, so the final tree edges are minimum cuts. Only symmetry and submodularity are used.

## Depends on

- [Gomory-Hu trees](gomory-hu-tree.md)

## Proof depends on

- [Uncrossing minimum cuts of symmetric submodular functions](uncrossing-minimum-cuts.md)

## Sources

- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
