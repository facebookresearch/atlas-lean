# Counted union returns the union's array

For a union-find structure $S$ and indices
$x, y$ of $S$, the array returned by the counted union of $x$ and $y$ in $S$ equals the node array
of the uncounted union of $x$ and $y$ in $S$ (union by rank with path compression).

## Depends on

- [Union by rank with operation counts](counted-union.md)
