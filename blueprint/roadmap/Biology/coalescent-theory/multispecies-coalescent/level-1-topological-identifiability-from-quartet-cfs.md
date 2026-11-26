# Topological identifiability of a level-1 species network from quartet CFs

Let $\mathcal{N}^+$ be a binary level-1 phylogenetic network on $n \ge 4$ taxa with generic numerical
parameters, and let $\widetilde{\mathcal{N}}$ be the semidirected topological network it induces, with
every $2$-cycle replaced by an edge, those cycles being unidentifiable. Under the network multispecies
coalescent with one gene lineage sampled per taxon, the topological structure of
$\widetilde{\mathcal{N}}$, including the directions of its hybrid edges, is identifiable from the quartet
concordance factors of $\mathcal{N}^+$, with exactly the following exceptions. Here a cycle **induces an
$(n_1,\dots,n_m)$ partition** when deleting its edges splits the taxa into blocks of those sizes, and the
**hybrid block** is the block descended from the hybrid node.

1. For a $3$-cycle inducing a $(1,1,n-2)$ partition: if the hybrid node has a single descendant taxon,
   the network cannot be distinguished from the network with the cycle contracted to a node, nor from the
   network with the hybrid and the other singleton block interchanged. If the hybrid node has $n-2$
   descendant taxa, there are positive-measure sets of parameters on which the semidirected $3$-cycle is
   identifiable and positive-measure sets on which it is not.
2. For a $3$-cycle inducing a $(1,n_1,n_2)$ partition with $n_1, n_2 \ge 2$: the undirected $3$-cycle is
   identifiable, and there are positive-measure sets of parameters on which the semidirected cycle is
   identifiable and positive-measure sets on which it is not.
3. For a $3$-cycle inducing an $(n_1,n_2,n_3)$ partition with all $n_i \ge 2$: the undirected $3$-cycle is
   identifiable and at least one of its nodes can be shown not to be the hybrid node, but again both the
   identifiable and the non-identifiable parameter sets have positive measure.
4. For a $4$-cycle inducing a $(1,1,1,1)$ partition: the location of the hybrid node is not identifiable.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [Quartet concordance factors depend only on the unrooted quartet network](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)
- [Identifiability of networks under the network multispecies coalescent](network-coalescent-identifiability-questions-spe.md)

## Proof depends on

- [Two-cycles of a level-1 network are not identifiable from quartet CFs](level-1-two-cycles-not-identifiable.md)
- [Identifiability of level-1 networks from orderings of quartet concordance factors](level-1-network-identifiability-from-quartet-concordance-factor-orderings.md)
- [Concordance-factor signatures of cycles in level-1 quartet networks](big-cycle-property-detects-4-cycles.md)
- [Three-cycles with a two-leaf hybrid are the source of four-taxon anomalies](three-two-cycles-and-four-taxon-anomalies.md)

## Expansion

The starting point is the earlier result that the network obtained by contracting all $2$- and $3$-cycles,
suppressing degree-$2$ nodes and undirecting the hybrid edges of $4$-cycles is identifiable from quartet
concordance factors for generic parameters; what remains is to decide what can be recovered about $2$-,
$3$- and $4$-cycles. Two-cycles are lost outright. Three-cycles are attacked with polynomial invariants of
the concordance factors: on a five-taxon tree the polynomial
$f_{abc} = 3\,\mathrm{CF}_{ab|ac}\,\mathrm{CF}_{ab|bc} - \mathrm{CF}_{ab|ab}$ vanishes, while it does not
vanish identically on the five-taxon networks whose central $3$-cycle contracts to that tree, so its
vanishing generically detects the absence of a $3$-cycle; the three variants $G_{abc}, G_{bca}, G_{cab}$
play the same role on six taxa and their signs carry partial information about which node is hybrid. The
positive-measure statements come from the fact that the parameters making a $3$-cycle visible are exactly
those making the induced quartet network anomalous, and both that set and its complement have positive
measure.

## Sources

- E. S. Allman, H. Baños, M. Garrote-López and J. A. Rhodes, "Identifiability of level-1 species networks from gene tree quartets", Bulletin of Mathematical Biology 86 (2024), 110, <https://doi.org/10.1007/s11538-024-01339-4> (PMC11272829). (Theorem 19, with Theorem 2, Proposition 6, Theorems 7, 15 and 17.)
