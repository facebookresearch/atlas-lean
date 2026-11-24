# Rank bounds for union-find built by the public operations

For the union-find structure stored as parent and rank arrays, the structures built by the public
operations (appending a node, find with path compression and union) keep every root's class of size
at least two to the power of its rank, so ranks and parent chains are at most the base-two logarithm
of the number of nodes.

- [Array union-find structures built by the public operations](reachable.md)
