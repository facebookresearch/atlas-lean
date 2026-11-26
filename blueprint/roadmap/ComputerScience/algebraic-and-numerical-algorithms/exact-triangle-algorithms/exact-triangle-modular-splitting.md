# Splitting Exact Triangle into lopsided triangle queries

Fix a prime $p$ in $[\sqrt{D}/2, \sqrt{D})$ and a group count $g \le \sqrt{D}$. Partition the third part of an Exact Triangle instance into pieces of size about $\sqrt{D}$, and partition the pairs of the first two parts by residue class of $A_{ij} \bmod p$ into chunks. Each (piece, chunk) pair defines a lopsided triangle query whose middle part consists of pairs (third-part vertex, residue label), with at most $D$ middle vertices, such that a triangle $(i, j, k)$ satisfies $A_{ij} + B_{jk} + C_{ik} \equiv 0 \pmod p$ if and only if the corresponding outer pair has a common neighbour in the query of its piece and chunk. The number of queries and their total size are bounded explicitly in $n$, $D$ and $g$, and the degree of each middle vertex is at most $O(n/g)$ when $g \le \sqrt{D}$.

## Depends on

- [Lopsided triangle queries](lopsided-triangle-queries.md)
- [Modular triangle counts and false positives](modular-triangle-counts.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", arXiv:2610.06783, 2026.
