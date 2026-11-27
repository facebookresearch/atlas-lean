# The (min,+) product as shortest distances in a layered graph

For $n \times n$ matrices $A, B$ over $\mathbb{Z} \cup \{+\infty\}$, let $T(A,B)$ be the digraph on three copies $\{0,1,2\} \times [n]$ of the vertex set with an arc $(0,i) \to (1,j)$ of weight $A_{ij}$ and an arc $(1,j) \to (2,k)$ of weight $B_{jk}$ (and no others). Then $T(A,B)$ has no cycles, in particular no negative cycles, and the shortest-path distance from $(0,i)$ to $(2,k)$ equals $(A \star B)_{ik}$. Hence the $(\min,+)$ product reduces to all-pairs shortest paths on $3n$ vertices.

## Depends on

- [Min-plus matrix powers give shortest path weights with at most $r$ edges](../all-pairs-shortest-paths-by-min-plus-products/matrix-pow-edge-bounded.md)
- [Negative cycles](../floyd-warshall-algorithm/is-negative-cycle.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
