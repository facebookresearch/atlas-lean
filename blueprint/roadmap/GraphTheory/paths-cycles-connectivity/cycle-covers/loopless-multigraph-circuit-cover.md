# Circuits and double covers of finite loopless multigraphs

A finite loopless multigraph has a finite vertex set and a separate finite set of edge objects, each with two distinct endpoints. Parallel edges remain distinct. A cut consists of all edge objects with exactly one endpoint in a given vertex subset; bridgeless means no such cut has cardinality one.

An even edge set has even degree at every vertex, counting edge ends. A circuit is a nonempty inclusion-minimal even edge set. In particular two distinct parallel edges form a circuit. A cycle double cover is a finite list of circuits in which every edge object belongs to exactly two list entries; two entries may be the same circuit. For an edgeless graph the empty list is allowed.

## Expansion

Use a finite multigraph model with separately indexed edges, not a simple-graph adjacency relation that merges parallel edges. Prove that the singleton-cut test matches deletion of a bridge and that minimal nonempty even edge sets agree with simple closed walks up to their edge sets, including digons and disconnected graphs.

## Sources

- [Pinned multigraph and cut definitions](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/GeneralGraph.lean#L16-L56)
- [Pinned even sets, circuits, and double-cover definitions](https://github.com/openai/cdc-lean/blob/577e9d9ea326d520f80672ee69b830bf1d513df5/CDCLean/CycleDecomposition.lean#L28-L106)
