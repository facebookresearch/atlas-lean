# Linear Erdős–Gallai cycle and single-edge decomposition

There is a real $C>0$ such that for all $n\in\mathbb N$ and every simple graph on $n$ labelled vertices, the edge set has a partition into $k$ pairwise disjoint parts with $k\le Cn$. Each part is either the set of edges of a closed simple cycle in the graph or the singleton of an existing edge. The union is the entire edge set; the parts need not be disjoint in vertices. An edgeless graph admits $k=0$.

## Depends on

- Simple graph edges and cycles, indexed edge-set partition allowing singleton edges.

## Proof outline

Separate the cycle and residual-edge bounds, merge the corresponding disjoint partitions, and check the empty graph and one-edge graph. Do not require cycles to be induced or forbid singleton edges.

- Cycle extraction and linear budget for residual edges, with a bound uniform over all finite simple graphs.

## Sources

- [Comparator statement: `OAI.ErdosGallai.erdos_gallai`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/CycleDecomposition.lean#L31-L33)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/181.md)
