# Union-find structures built by make-set, find and union

The union-find structures obtained from the empty structure by make-set (appending a new
singleton node), find with path compression, and union by rank (two finds and a link). These are the structures that occur along the operation sequences analysed by
Tarjan and van Leeuwen; the rank bounds of this topic hold for all of them.

## Related topics

- [Array union-find structures built by the public operations](reachable-state-rank-bounds-for-canonical-union/reachable.md): the same family for the union-find structure stored as parent and rank arrays.

## Sources

- R. E. Tarjan and J. van Leeuwen, *Worst-case analysis of set union algorithms*, J. ACM 31(2)
  (1984) 245–281, §1.
