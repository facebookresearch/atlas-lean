# Neighbor joining forms the splits of a tree when every join forms a side

Let `(G, ι)`
be a binary phylogenetic `X`-tree and `D` any dissimilarity. Suppose that whenever a run of
neighbor joining on `D` has reached a partition `S` of the taxa into sides of edges of the tree
(with at least four clusters) and joins two of its clusters, their union is again a side of an
edge. Then every complete run of neighbor joining on `D` (stopped with at most three clusters)
forms exactly the splits of the internal edges of the tree. This reduces the correctness of
neighbor joining on `D` to its selection step.
