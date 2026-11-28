# Tnbp reachable of avoid

Removing a non-cut vertex. If `G'` is `G` with the vertex `c` removed and the neighbours of
`c` are pairwise connected in `G'`, then any two vertices other than `c` that are connected in
`G` are connected in `G'`. This is the vertex analogue of Mathlib's
`SimpleGraph.Reachable.reachable_deleteEdges_of_not_isBridge` for edges.
