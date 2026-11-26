# Frontier-minimal splits graphs of level-1 networks and consistency of NANUQ

Let $N^+$ be a binary level-1 rooted phylogenetic network on $X$ and $N^-$ its unrooted semidirected network, with split system $S(N^-)$ (the union of the split sets of its displayed trees).

**Theorem (frontier of the splits graph).** The frontier of any frontier-minimal splits graph for the circular split system $S(N^-)$ is the graph obtained from $N^-$ by

1. contracting every 2- and 3-cycle,
2. undirecting the hybrid edges of every 4-cycle,
3. replacing every $m$-cycle with $m \ge 5$ by the frontier of an $m$-dart whose point sits at the hybrid node, the $m$ edges leaving the cycle attached to the corners of the dart in the cyclic order of the cycle.

In particular the tree of blobs of $N^-$ is isomorphic to that of any frontier-minimal splits graph for $S(N^-)$, and, under the network multispecies coalescent with generic parameters, $N^-$ with 2- and 3-cycles suppressed and 4-cycles undirected is identifiable from quartet concordance factors.

**Theorem (statistical consistency of NANUQ).** Consider the NMSC on a binary level-1 metric network $N^+$ whose induced quartet networks with $3_2$-cycles all have tree-like concordance factors with a unique largest entry. (Tree-like concordance factors, two equal smallest entries, include the star point $(1/3, 1/3, 1/3)$, which a binary $3_2$-cycle quartet network can attain with positive edge lengths, so this uniqueness is a hypothesis, not a consequence of the binary topology.) NANUQ (per-quartet hypothesis tests on gene-tree quartet counts at levels $\alpha, \beta$, the network quartet distance, NeighborNet, then a circular-network splits graph) admits a sequence $\alpha_m \in (0,1)$, $\alpha_m \to 0$, such that for every $\beta \in (0, 1)$ the algorithm run on $m$ independent gene trees at levels $\alpha_m, \beta$ outputs the network described in the first theorem with probability tending to $1$ as $m \to \infty$.

## Expansion

The first theorem combines the circularity of $S(N^-)$ with a characterization of frontier-minimal splits graphs (the authors' Lemma 28 and Proposition 30, the latter showing that the Circular Network Algorithm produces one) and an analysis of how the displayed trees of each cycle of $N^-$ contribute splits. For consistency, as $m \to \infty$ the per-quartet tests classify every quartet as tree or 4-cycle network correctly with probability tending to $1$. The star test rejects its null on a quartet only when the true concordance factors are not $(1/3, 1/3, 1/3)$: for quartets whose concordance factors are those of a resolved quartet tree with a positive internal length this holds automatically, and for the tree-like $3_2$-cycle quartets it is the unique-largest-entry hypothesis. So the empirical network quartet distance coincides with the true one; that distance is circular with support $S(N^-)$, so NeighborNet and the Circular Network Algorithm return the frontier described in the first theorem.

## Depends on

- [Network quartet distance and the grove of displayed trees](network-quartet-distance-grove-identity.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](../multispecies-coalescent/network-multispecies-coalescent-fixed-network-ge.md)
- [Quartet concordance factors depend only on the unrooted quartet network](../multispecies-coalescent/quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)

## Proof depends on

- [Concordance-factor signatures of cycles in level-1 quartet networks](../multispecies-coalescent/big-cycle-property-detects-4-cycles.md)
- [Identifiability of level-1 networks from orderings of quartet concordance factors](../multispecies-coalescent/level-1-network-identifiability-from-quartet-concordance-factor-orderings.md)

## Sources

- E. S. Allman, H. Baños and J. A. Rhodes, "NANUQ: a method for inferring species networks from gene trees under the coalescent model", *Algorithms for Molecular Biology* 14 (2019), 24, <https://doi.org/10.1186/s13015-019-0159-2> (PMC6896299). Theorem 34, Corollaries 31 and 35, Theorem 36.
