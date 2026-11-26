# Proportional priors on joint species-delimitation and species-tree models

Let $s \ge 3$ populations be given, none of which may be split. A guide tree is a rooted binary tree on the $s$ populations; there are $(2s-3)!! = 1 \cdot 3 \cdots (2s-3)$ of them. A representation of a joint model of species delimitation and species phylogeny is a guide tree together with a set $U$ of its internal nodes that is closed under taking ancestors (possibly empty): the nodes in $U$ stay resolved, every other internal node is collapsed, the populations below each collapsed maximal subtree form one species, and the number of delimited species is $|U| + 1$. The species tree of a representation is the guide tree restricted to $U$, with the merged groups as leaves.

Two priors are defined by proportional weights over representations:

- **Prior 0** gives each representation weight equal to the number of labelled histories (rankings of internal nodes by age compatible with the tree) of its species tree.
- **Prior 1** gives every representation weight $1$.

Writing $P_d$ for the induced prior probability of $d$ delimited species, the values are

| $s$ | Prior 0: $(P_1, \dots, P_s)$ | Prior 1: $(P_1, \dots, P_s)$ |
|---|---|---|
| 3 | $(1/3, 1/3, 1/3)$ | $(1/3, 1/3, 1/3)$ |
| 4 | $(5/22, 5/22, 6/22, 6/22)$ | $(5/21, 5/21, 6/21, 5/21)$ |
| 5 | $(7/47, 7/47, 9/47, 12/47, 12/47)$ | $(7/40, 7/40, 9/40, 10/40, 7/40)$ |

Under Prior 1, for every $s \ge 3$, $P_1 = P_2 = P_s$.

## Depends on

- [Rooted binary species tree with branch lengths](../../../coalescent-theory/multispecies-coalescent/species-tree.md)
- [Ranked labeled history](../../../coalescent-theory/ranked-labeled-histories-of-coalescent-trees/ranked-history.md)

## Proof depends on

- [Schröder's count of rooted binary phylogenetic trees](../../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/nat-card-rooted-binary-tree.md)

## Expansion

Every guide tree has exactly one representation with $U = \varnothing$ (one species), exactly one with $U$ equal to the root alone (two species), and exactly one with $U$ equal to all internal nodes ($s$ species). Under Prior 1 each of the three classes therefore receives total weight $(2s-3)!!$, which proves $P_1 = P_2 = P_s$. For $s = 4$ the 12 caterpillar guide trees generate 4 representations each and the 3 balanced trees generate 5 each, so the Prior 1 normalizing constant is $12 \cdot 4 + 3 \cdot 5 = 63$; under Prior 0 the fully resolved balanced tree has 2 labelled histories, giving $Z = 12 \cdot 4 + 3 \cdot 6 = 66$. Both priors put the same mass on the several representations of one biological model (for instance the one-species model appears once per guide tree), and both favour fewer species than a uniform prior over the 7, 41, 346 and 3797 distinct models for $s = 3, 4, 5, 6$, or than a uniform prior over the $5, 15, 52, 203$ delimitations (Bell numbers). Under the multispecies coalescent the posterior then weights each representation by its marginal likelihood, integrated over population sizes $\theta$, divergence times $\tau$ and the gene trees.

## Sources

- Yang Z, Rannala B. Unguided species delimitation using DNA sequence data from multiple loci. *Molecular Biology and Evolution* 31:3125–3135 (2014), section "Priors on Species Delimitation and Species Phylogeny", Table 1, and Discussion. DOI <https://doi.org/10.1093/molbev/msu279>. PMCID PMC4245825.
