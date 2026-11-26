# Identifiability of level-1 networks from orderings of quartet concordance factors

Let $N^+$ be a metric rooted level-1 network on a taxon set $X$ with $|X| \ge 4$, gene trees arising under the network multispecies coalescent, and let $N^-$ be the induced unrooted semidirected network. For each four-taxon set $s \subseteq X$ consider only the ordering of the three entries of $\mathrm{CF}_s$ (which entries are larger, smaller or equal), not their values.

**Statement.** For generic numerical parameters, the collection of orderings of quartet concordance factors over all four-taxon subsets identifies the unrooted semidirected topological network $\tilde N$ obtained from $N^-$ by contracting all 2-cycles and 3-cycles and forgetting the directions of the hybrid edges in 4-cycles, while retaining the directions of the hybrid edges of every $k$-cycle with $k \ge 5$. In particular, for each cycle of size $k_v \ge 4$ with hybrid node $v$:

1. the partition of the taxa into $v$-blocks and the cycle size $k_v$ are identified from the set of four-taxon subsets satisfying the Big Cycle property;
2. the cyclic order of the $v$-blocks around the cycle is identified;
3. if $k_v \ge 5$, the hybrid block (the taxa below $v$) is identified.

Moreover, if a set $\{a, b, c, d\}$ satisfies the Cycle property but not the Big Cycle property and no fifth taxon $e$ makes any $\{i, j, k, e\}$ with $i, j, k \in \{a, b, c, d\}$ satisfy the Big Cycle property, then $N^-$ contains a 3-cycle with at least two descendants of its hybrid node.

## Depends on

- [Concordance-factor signatures of cycles in level-1 quartet networks](big-cycle-property-detects-4-cycles.md)
- [Identifiability of networks under the network multispecies coalescent](network-coalescent-identifiability-questions-spe.md)

## Proof depends on

- [An unrooted binary tree is determined by its induced quartet trees](../../phylogenetics/quartet-support-and-determination-of-trees-by-qu/iso-of-induces-iff.md)

## Expansion

The proof is by induction on the number of cycles of size at least 4. With none, every quartet network is treelike after contracting 2- and 3-cycles, the orderings give each induced quartet tree, and quartet trees determine the tree. For generic parameters, a set satisfying the Big Cycle property exists for a cycle $C_v$ exactly when $C_v$ has size $k_v \ge 4$ and the four taxa lie in distinct $v$-blocks, one of them the hybrid block. Two such sets sharing three taxa determine the same hybrid node, which lets the sets be grouped by cycle and the $v$-blocks and $k_v$ be reconstructed; which concordance factor is smallest records which blocks are adjacent, giving the cyclic order. The hybrid block itself is recovered only when $k_v \ge 5$, so the directions of hybrid edges in 4-cycles are not identified.

## Sources

- H. Baños, "Identifying species network features from gene tree quartets under the coalescent model", Bulletin of Mathematical Biology 81 (2019), <https://doi.org/10.1007/s11538-018-0485-4> (PMC6344282). Lemmas 12–16, Theorem 4 and Proposition 12.
