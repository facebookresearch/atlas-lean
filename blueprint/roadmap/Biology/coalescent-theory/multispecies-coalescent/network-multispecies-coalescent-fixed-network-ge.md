# Network multispecies coalescent: the gene-tree probability kernel of a fixed network

Let $\mathcal{N}$ be a rooted, time-consistent phylogenetic network: a directed acyclic graph with well-labelled leaves, tree nodes, and reticulation nodes, each reticulation carrying an inheritance probability $\gamma \in [0, 1]$ for one of its two parent edges. Its branches have nonnegative coalescent lengths and its root population is infinite.

Gene lineages evolve backwards in time as follows. Within each branch they coalesce as in Kingman's coalescent, as in [the multispecies coalescent](gene-tree-prob.md). Each lineage that reaches a reticulation chooses its parent edge independently of all other lineages, with probabilities $\gamma$ and $1 - \gamma$. Correlated inheritance is excluded.

The induced law of the gene tree is a probability kernel in the network data: the probabilities of all gene trees sum to $1$. When every $\gamma \in \{0, 1\}$ it reduces to the gene tree probability of [the multispecies coalescent](gene-tree-prob.md) on the species tree that the network then displays.

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)
- [Phylogenetic network (routing skeleton)](../../population-structure/admixture-graphs/phylo-network.md)
- [Routing kernel of a phylogenetic network](../../population-structure/admixture-graphs/route-prob-2.md)

## Expansion

1. Normalization of the kernel, by induction over the network from the leaves.
2. The reduction for $\gamma \in \{0, 1\}$.
3. A check: one reticulation and two lineages, where the explicit mixture over the four routings sums to $1$.

## Sources

- C. Meng and L. S. Kubatko, Detecting hybrid speciation in the presence of incomplete lineage sorting using gene tree incongruence: a model, *Theor. Popul. Biol.* 75 (2009), 35–45 (network coalescent).
