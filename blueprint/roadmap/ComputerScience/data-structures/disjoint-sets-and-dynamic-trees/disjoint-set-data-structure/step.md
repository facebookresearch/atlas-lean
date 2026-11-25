# One set-union operation with its cost

The cost model for union-find with linking by rank and find with path compression, following
Tarjan and van Leeuwen. A make-set appends a new singleton node and costs $1$. A find on a node
$x$ compresses the find path of $x$ and costs the number of nodes on that path, that is, the
[find path length](find-path-length.md) of $x$ plus one. A union on nodes $x$ and $y$ performs a
find on $x$, then a find on $y$ in the compressed structure, then a link by rank of the two
roots, and costs the costs of the two finds (the second measured in the compressed structure)
plus $1$. A find on an index that is not a node, or a union in which $x$ or $y$ is not a node,
changes nothing and costs $1$.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §1 (make set, find, link and unite) and §3 (the time of a sequence is bounded
  by a constant times $n$ plus the total number of nodes on find paths).
