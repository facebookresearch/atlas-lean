# Distinguishing level-2 galled networks by quartets and NANUQ distances

**Setting.** Semi-directed phylogenetic networks on a leaf set $X$ that are level-2 (each blob has at most two reticulations), outer-labeled planar (an embedding in the plane with leaves on the outer face) and galled (every reticulation lies in a tree cycle). The canonical form of such a network contracts the features invisible to quartet data (2-blobs, 3-blobs and 3-cycles within blobs, and unresolvable hybrid placements). For a network $N$ let $\mathcal Q(N)$ be its set of displayed quartets and $\mathcal T(N)$ its displayed trees.

**Theorem.** (a) Two semi-directed, outer-labeled planar, level-2, galled networks $N_1,N_2$ are distinguishable from their displayed quartets iff their canonical forms differ. Equivalently, the following are equivalent: $N_1,N_2$ have isomorphic canonical forms; $\mathcal Q(N_1)=\mathcal Q(N_2)$; $\mathrm{Split}(\mathcal T(N_1))=\mathrm{Split}(\mathcal T(N_2))$.

(b) Two such networks that are moreover bloblet networks (a single nontrivial blob with all leaves attached to it) on at least four leaves are distinguishable from their pairwise NANUQ distances iff their canonical forms differ.

**Consequence.** For data generated under the network multispecies coalescent, quartet concordance factors are consistently estimated from gene trees, so a NANUQ-type distance method followed by circular split decomposition consistently recovers the canonical form for these level-2 networks, extending consistency results previously limited to level-1 networks.

## Depends on

- [Circular decomposability of quartet-based network metrics](circular-decomposability-of-quartet-based-network-metrics.md)

## Expansion

Displayed quartets and the split system of the displayed trees determine each other through the displayed quartet metric, whose support is $\mathrm{Split}(\mathcal T(N))$; this gives the equivalence of the three conditions in (a). The remaining work is to show that, up to the contractions defining the canonical form, an outer-labeled planar galled level-2 network is determined by that split system. In (b) the NANUQ metric has the same support on bloblets, and its split weights additionally separate configurations with equal displayed splits; for example, the pairwise NANUQ distances already distinguish the five canonical classes of 6-taxon level-2 bloblets.

## Sources

- N. Holtgrefe, E. S. Allman, H. Baños, L. van Iersel, "Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances", *Bulletin of Mathematical Biology* 87(12) (2025), 168, Section 5 (Proposition 5.3, Theorem 5.4), <https://doi.org/10.1007/s11538-025-01549-4> (preprint arXiv:2507.17308).
