# Tripartition characterization of groves and failure of the grove union conjecture

Let $\mathcal S = \{X_1,\dots,X_m\}$ be a set of taxon sets with union $\mathcal L(\mathcal S)$. A **topology assignment** on $\mathcal S$ is a choice of one rooted phylogenetic tree on each $X_i$ such that all these trees are compatible (displayed by a common *supertree*). For a partition $\pi = S_1|\cdots|S_k$ of $\mathcal S$, a **cross triple** is a set $\{x,y,z\}\subseteq\mathcal L(\mathcal S)$ of taxa not all contained in the taxon sets of a single block $S_i$; it is **resolved** if some topology assignment makes all its supertrees display the same rooted tree on $\{x,y,z\}$, and an assignment is *informative* for $\pi$ if it resolves some cross triple. $\mathcal S$ is a **grove** if for every partition $\pi$ of $\mathcal S$ either there is no cross triple with respect to $\pi$ or there is an informative topology assignment with respect to $\pi$. A grove in a database $\mathcal D$ is *maximal* if no further taxon set of $\mathcal D$ can be added keeping the grove property. The **2-overlap graph** of $\mathcal S$ joins $X_i$ and $X_j$ when $|X_i\cap X_j|\ge 2$.

**Theorem.**

1. (Tripartition characterization.) $\mathcal S$ is a grove if and only if the grove condition holds for every split (bipartition) and every tripartition of $\mathcal S$.
2. (Grove union conjecture fails.) The statements "the maximal groves of a database partition it", "the union of two intersecting groves is a grove" and "two distinct maximal groves are disjoint" are equivalent, and all three are false in general: there are intersecting groves whose union is not a grove. The same failure occurs for informative groves, and the union of intersecting strictly informative groves need not be strictly informative even when it is a grove.
3. (2-overlap groves.) Every set of taxon sets with connected 2-overlap graph is a grove, and if two such 2-overlap groves intersect, their union again has connected 2-overlap graph. Hence within the class of 2-overlap groves the maximal ones partition the database, namely into the connected components of its 2-overlap graph.

## Depends on

- [Splits, compatibility, ultrametrics and UPGMA](../../splits-compatibility-ultrametrics-and-upgma/README.md)

## Expansion

For item 1, given a cross triple $\{x,y,z\}$ for an arbitrary partition $\pi$, merge the blocks of $\pi$ into at most three groups according to which two of $x, y, z$ they contain (and a group for the rest); $\{x,y,z\}$ is still a cross triple for this coarser split or tripartition, a triple resolved there remains a cross triple for $\pi$, and the same topology assignment resolves it. For item 2, the three statements are equivalent by elementary arguments on maximality; an explicit small family of taxon sets gives two intersecting groves whose union has a partition with cross triples none of which any compatible assignment can resolve. For item 3, two taxon sets sharing at least two taxa can be assigned trees that force a resolution of a cross triple across them, and connectivity of the 2-overlap graph propagates this across any partition; intersecting connected subgraphs have connected union.

## Sources

- Mareike Fischer, "Mathematical aspects of phylogenetic groves", arXiv (2011). Section 2 (topology assignments, cross triples, groves), Theorem 3.7, Lemma 3.8, Propositions 3.9, 3.11, 3.12, Theorem 3.16, Corollary 3.17, Theorem 3.18. <https://doi.org/10.48550/arXiv.1104.2562>. Published version: Annals of Combinatorics 17(2) (2013), 295–310, <https://doi.org/10.1007/s00026-013-0179-4>; locators above refer to the arXiv version.
