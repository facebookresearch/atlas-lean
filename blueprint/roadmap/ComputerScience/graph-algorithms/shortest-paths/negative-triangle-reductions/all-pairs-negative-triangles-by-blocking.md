# All pairs negative triangles by blocking

Split each of the three parts of an $n$-vertex-per-part tripartite graph into $t$ blocks. Using a procedure that finds a negative triangle (or reports none) in a block triple at cost at most $\tau$, APNT can be solved at cost at most $(t^3 + n^2)\,\tau$: for every block triple, repeatedly find a negative triangle $(i, j, k)$, record the pair $(i, j)$ and delete the edge $ij$ from $C$, until the block triple has none.

## Proof sketch

Each block triple has exactly one unsuccessful call; each successful call deletes a distinct $C$-edge, and there are at most $n^2$ such edges.

## Depends on

- [Negative triangles in tripartite weighted graphs](negative-triangle.md)

## Proof depends on

- [Finding a negative triangle from a detector](finding-negative-triangle-from-detection.md)

## Sources

- V. Vassilevska Williams and R. Williams, "Subcubic Equivalences Between Path, Matrix, and Triangle Problems", Journal of the ACM 65(5), 2018.
