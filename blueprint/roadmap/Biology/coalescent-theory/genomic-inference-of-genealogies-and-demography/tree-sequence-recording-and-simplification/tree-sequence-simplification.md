# Tree sequence simplification

Let $(N, E)$ be [valid node and edge tables](valid-node-and-edge-tables.md) on $[0, L)$, and let $S$ be a set of sample nodes. The **simplification** of $(N, E)$ with respect to $S$ is a tree sequence $(N', E')$, with the samples relabelled $0, \dots, |S| - 1$, that satisfies:

1. **Same genealogies:** at every position $x$, the marginal tree of $(N', E')$ equals the subtree of the input marginal tree at $x$ induced by $S$.
2. **No unary vertices:** in every marginal tree, every non-sample vertex has at least two children.
3. **Only ancestral material:** every node and edge not ancestral to some sample at the relevant positions is removed.
4. **No adjacent redundant edges:** no two edges $(\ell, x, p, c)$ and $(x, r, p, c)$ remain; they are merged into $(\ell, r, p, c)$.

The output nodes are numbered with the samples first, then in order of birth time.

**Algorithm.** Process the input parents in order of increasing time ago. The state is a set of ancestral lineages, each a list of segments $(\ell, r, u)$ meaning output node $u$ inherits $[\ell, r)$ through that lineage. Each input edge $(\ell, r, p, c)$ passes the parts of $c$'s segments that overlap $[\ell, r)$ up to $p$. Where two or more segments overlap inside one parent, that parent becomes an output node on the overlap: the edges to the overlapping output nodes are recorded and the overlap is replaced by one segment for the new node. All coalescing segments in one parent share a single new output node. A segment stops propagating once all samples have coalesced on it. The running time is linear in the number of input edges, up to the work spent writing the output.

**Uses.** Simplifying periodically during a forward simulation, with $S$ the living population, bounds memory without changing the genealogy of the survivors. A simulation can also start from a tree sequence of prior history, for example one produced by a coalescent simulation.

## Depends on

- [Valid node and edge tables define a forest at every genomic position](valid-node-and-edge-tables.md)
- [Coalescence records encode a sequence of local trees exactly](../../two-locus-coalescent/tree-sequence-encoding-represents-local-trees-ex.md)

## Expansion

The algorithm is Hudson's backwards ancestry tracing with the coalescence events fixed by the recorded pedigree rather than drawn at random. Think of each sample's chromosome as painted its own colour. Going back in time, colours are copied onto the parental segments they were inherited from. Where two colours would land on the same spot, a coalescence is recorded as edges to a new node with a fresh colour, and a fully coalesced segment is dropped. Each recorded edge joins an output node to the nearest ancestor in which that segment coalesces with another lineage, so unary vertices never appear (property 2). Only segments reached from samples are touched (property 3). The induced subtrees are reproduced exactly (property 1). Merging contiguous segments with the same parent and child gives property 4. Every input edge is examined once in time order, which gives the linear dependence on input size.

## Sources

- J. Kelleher, K. R. Thornton, J. Ashander and P. L. Ralph, "Efficient pedigree recording for fast population genetics simulation", *PLoS Computational Biology* 14(11) (2018), e1006581, <https://doi.org/10.1371/journal.pcbi.1006581> (PMC6233923), sections "Tree sequence simplification", "Sequential simplification and prior history" and "Computational complexity"; pseudocode in S1 Text.
