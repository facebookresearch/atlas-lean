# Rank bounds for union-find built by the public operations

For the union-find structure stored as parent and rank arrays, the structures built by the public
operations (appending a node, find with path compression and union) keep every root's class of size
at least two to the power of its rank, so ranks and parent chains are at most the base-two logarithm
of the number of nodes. The bound $2^{r} \le$ class size is the [rank bound for union by rank](../two-pow-rank-le-class-size.md), stated there for the same structures.

- [Array union-find structures built by the public operations](reachable.md)
- [Component](component.md)
- [Mem component](mem-component.md)
- [Empty](empty.md)
- [Rank root D le log2](rank-root-d-le-log2.md)
- [Ranks grow along nonroot parent steps](rank-add-le-rank-iterate.md)
- [First root on a parent chain within the rank gap](exists-first-iterate-root-d-le-rank.md)
- [First root on a parent chain within log₂ of the size](exists-first-iterate-root-d-le-log2.md)
