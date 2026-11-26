# Quartet concordance factors depend only on the unrooted quartet network

Let $N^+$ be a metric binary rooted level-1 phylogenetic network on a taxon set $X$: a rooted directed acyclic graph with tree and hybrid edges, edge lengths $\lambda > 0$ (in coalescent units) and inheritance probabilities $\gamma \in (0, 1)$ on hybrid edges, summing to $1$ over the two hybrid edges entering each hybrid node, in which no two cycles of the underlying undirected graph share an edge. Under the network multispecies coalescent (NMSC), for distinct taxa $a, b, c, d$ and one gene sampled from each, the quartet concordance factors are

$$\mathrm{CF}_{abcd} = \big(\mathrm{CF}_{AB|CD},\ \mathrm{CF}_{AC|BD},\ \mathrm{CF}_{AD|BC}\big),$$

where $\mathrm{CF}_{AB|CD}$ is the probability that the gene tree displays the split $AB|CD$.

For $Z \subseteq X$, the lowest stable ancestor $\mathrm{LSA}(Z)$ is the lowest node lying on every directed path from the root to every $z \in Z$. Let $Q^{\oplus}_{abcd}$ be the induced network on $\{a, b, c, d\}$ with everything above $\mathrm{LSA}(a, b, c, d)$ deleted, and $Q^{-}_{abcd}$ the induced unrooted semidirected quartet network (root suppressed, tree edges undirected, hybrid-edge directions kept).

**Statement.**

1. $\mathrm{CF}_{abcd}$ can be computed from $Q^{\oplus}_{abcd}$: the chain of 2-cycles that can sit above the LSA in a level-1 network has no effect on quartet concordance factors.
2. If two metric level-1 LSA quartet networks induce the same unrooted network $Q^{-}_{abcd}$, they have the same concordance factors. Hence $\mathrm{CF}_{abcd}$ is a function of $Q^{-}_{abcd}$ alone, independent of the placement of the root compatible with the hybrid-edge directions.
3. For a species tree with unrooted quartet topology $ab|cd$ and internal edge of length $t$, $\mathrm{CF}_{abcd} = \big(1 - \tfrac23e^{-t},\ \tfrac13e^{-t},\ \tfrac13e^{-t}\big)$.

## Depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)

## Proof depends on

- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [Probability of quartet split 02|13 on the balanced tree](gene-tree-prob-balanced-split-02.md)

## Expansion

If fewer than four lineages reach the LSA, a coalescence below it has already fixed the unrooted gene-tree topology; if four lineages reach it, exchangeability of lineages under the coalescent makes all labelings of each rooted shape equally likely whatever happens above, which proves part 1. Part 2 is proved by induction on the number of cycles in $Q^{-}_{abcd}$: conditioning on the number of lineages entering each cycle's hybrid node and on which parent each lineage follows expresses the concordance factors as mixtures, with coefficients built from $\gamma$, of the concordance factors of networks with fewer cycles, and these mixtures depend only on the unrooted structure. Part 3 is the tree base case.

## Sources

- H. Baños, "Identifying species network features from gene tree quartets under the coalescent model", Bulletin of Mathematical Biology 81 (2019), <https://doi.org/10.1007/s11538-018-0485-4> (PMC6344282). Definitions 1–14, Equation (1), Theorem 2, Proposition 5 and Corollary 3.
