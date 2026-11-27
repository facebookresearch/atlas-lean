# Rank lower bounds from row and column sparsity

Over every field, if every row of a matrix $M$ has at most $d$ nonzero entries, then the number of nonzero columns of $M$ is at most $d\cdot\operatorname{rank}M$; if moreover every column has at most $e$ nonzero entries, then the total number of nonzero entries is at most $de\cdot\operatorname{rank}M$.

## Proof sketch

A row basis of $\operatorname{rank}M$ rows spans all rows, so every nonzero column is nonzero in some basis row, and the basis rows have at most $d\operatorname{rank}M$ nonzero positions in total; each nonzero column then contributes at most $e$ entries.

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
