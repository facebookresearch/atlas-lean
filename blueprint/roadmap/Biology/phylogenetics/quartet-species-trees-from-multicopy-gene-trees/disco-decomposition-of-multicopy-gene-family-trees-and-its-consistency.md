# DISCO decomposition of multicopy gene family trees and its consistency

**Decomposition.** Let $g$ be an unrooted gene family tree whose leaves are labelled by species,
possibly with several copies per species because of gene duplication and loss (GDL). DISCO
(Decomposition Into Single COpy gene trees) proceeds in two steps:

1. root $g$ and tag every internal node as a speciation or a duplication, using the ASTRAL-Pro
   rooting-and-tagging rule (root on the edge minimizing the number of duplication and loss events
   needed to explain the tree);
2. traverse the rooted tree in postorder; at every node tagged as a duplication, delete the edge
   above the child clade containing fewer species (ties broken arbitrarily), and keep the separated
   clade as a separate tree.

The output is a set of leaf-disjoint subtrees of $g$, each single-copy (no species repeated): one
possibly large tree and all clades split off during the traversal. If the rooting and tagging are
correct, every output tree contains only orthologs, since all duplication nodes have been removed.

**Theorem.** Consider a model of gene evolution in which GDL is the only cause of gene tree
discordance and the unrooted species tree topology has strictly positive probability of appearing
as a gene tree. If ASTRAL-Pro correctly roots and tags every gene family tree, then ASTRAL applied
to the DISCO trees (ASTRAL-DISCO) is a statistically consistent estimator of the unrooted species
tree as the number of gene families tends to infinity.

## Expansion

With correct tagging, each DISCO tree $t$ contains orthologs only, so the species tree $S$ restricted
to $L(t)$ equals $t$: $S$ is a compatibility supertree of all DISCO trees and agrees with every one of
them on every quartet. Hence $S$ attains the maximum possible score for the maximum quartet support
species tree problem on the decomposed trees. As the number of genes grows, almost surely some gene
tree has exactly the species tree topology; once it is present, any other tree disagrees with it on
at least one quartet, so $S$ is the unique optimum, and $S$ is feasible for ASTRAL's constrained
search because the constraint set contains every bipartition of every input tree. The guarantee
matches the one known for ASTRAL-Pro (which also assumes correct rooting and tagging), and both are
consistent under the multispecies coalescent alone, where all gene trees are single-copy and DISCO
is the identity. Splitting off the smaller clade at each duplication keeps one large single-copy
tree, which retains more quartets for the summary method than keeping only small orthologous
groups.

## Sources

- J. Willson, M. S. Roddur, B. Liu, P. Zaharias, T. Warnow, "DISCO: Species Tree Inference using
  Multicopy Gene Family Tree Decomposition", Systematic Biology 71 (2022), decomposition
  procedure (Algorithm 1) and Theorem 1, <https://doi.org/10.1093/sysbio/syab070> (PMC9016570).
