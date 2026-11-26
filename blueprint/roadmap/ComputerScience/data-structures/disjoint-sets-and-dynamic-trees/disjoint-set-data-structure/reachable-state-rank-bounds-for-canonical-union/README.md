# Rank bounds for union-find built by the public operations

For the union-find structure stored as parent and rank arrays, the structures built by the public
operations (appending a node, find with path compression and union) keep every root's class of size
at least two to the power of its rank, so ranks and parent chains are at most the base-two logarithm
of the number of nodes.

- [Array union-find structures built by the public operations](reachable.md)
- [Component](component.md)
- [Mem component](mem-component.md)
- [Empty](empty.md)
- [Two pow rank le card component](two-pow-rank-le-card-component.md)
- [Rank root D le log2](rank-root-d-le-log2.md)
- [Rank add le rank iterate](rank-add-le-rank-iterate.md)
- [Exists first iterate root D le rank](exists-first-iterate-root-d-le-rank.md)
- [Exists first iterate root D le log2](exists-first-iterate-root-d-le-log2.md)
