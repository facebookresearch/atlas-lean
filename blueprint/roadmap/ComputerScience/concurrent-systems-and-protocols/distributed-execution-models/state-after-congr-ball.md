# Locality in the LOCAL model

After `k` rounds, the state of a node `v` depends only on
its radius-`k` ball. Let `G` and `G'` be simple graphs on the same finite set of nodes, and let
the identifiers `ids`, `ids'` and the inputs `x`, `x'` agree at every node at distance at most
`k` from `v` in `G`, and the neighbours of every node at distance less than `k` from `v` be the
same in `G` and `G'`. Then `v` is in the same state after `k` rounds of any algorithm `A` in
both executions. Edges between two nodes at distance exactly `k` are not constrained.

## Sources

- N. Linial, *Locality in distributed graph algorithms*, SIAM Journal on Computing 21(1), 1992, 193–201, §2.
