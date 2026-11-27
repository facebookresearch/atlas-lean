# Linear-time sparse connectivity certificates by scan-first search (Nagamochi-Ibaraki)

For an undirected multigraph $G$ with $n \ge 1$ vertices and $m$ edges (parallel edges counted with multiplicity), a forest decomposition $F_1, F_2, \dots$ of $G$ can be computed in $O(n + m)$ time by a single scan-first search that assigns every edge the index of its forest. Consequently, for every $k$, a $k$-edge-connectivity certificate with at most $k(n-1)$ edges is computable in $O(n + m)$ time. Moreover, every $k$-vertex-connected graph $G$ has a $k$-vertex-connected spanning subgraph with $O(kn)$ edges, also computable in linear time.

## Proof sketch

Scan vertices in an order that always picks an unscanned vertex with the largest number of already scanned incident edges (counted over parallel edges); when scanning $u$, each unscanned edge $uv$ is placed into forest $F_{r(v)+1}$, where $r(v)$ is the number of previously labeled edges at $v$, and $r(v)$ is incremented. A bucket queue implements the order in linear time, and the scan-first property ensures that each $F_i$ is a maximal spanning forest of the graph remaining after removing $F_1, \dots, F_{i-1}$. The certificate claim then follows from the forest union lemma, and the vertex version follows from the same scan applied with the analogous local vertex-connectivity invariant.

## Depends on

- [Sparse k-edge-connectivity certificates and forest decompositions](sparse-k-edge-connectivity-certificate.md)
- [$k$-vertex-connected graph](../vertex-connectivity/is-vertex-connected.md)

## Proof depends on

- [Unions of the first k forests are k-edge-connectivity certificates](forest-union-certificate.md)
- [Menger's theorem for vertex cuts and internally disjoint paths](../menger-s-theorem/menger-vertex-max-min.md)

## Sources

- Hiroshi Nagamochi, Toshihide Ibaraki, "A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph", Algorithmica (1992).
