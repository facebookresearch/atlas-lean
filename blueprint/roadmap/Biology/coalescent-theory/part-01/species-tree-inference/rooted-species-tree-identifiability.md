# Identifiability of the rooted species tree from unrooted gene trees

Under the multispecies coalescent with one lineage sampled per taxon, Allman, Degnan and Rhodes (2011, Theorem 9) show that the distribution of unrooted gene tree topologies determines the rooted metric species tree $\sigma^+$ (the rooted topology and all internal edge lengths in coalescent units) when there are at least $5$ taxa, while for $4$ taxa it determines only the unrooted metric species tree $\sigma^-$. For four taxa (Proposition 3), the rooted trees $(((a, b){:}x, c){:}y_1, d)$, $(((a, b){:}x, d){:}y_2, c)$, $(((c, d){:}x, a){:}y_3, b)$, $(((c, d){:}x, b){:}y_4, a)$ and $((a, b){:}z, (c, d){:}x - z)$ with $x > z > 0$ give the same unrooted gene tree distribution. For any taxon set the distribution determines $\sigma^-$ (Corollary 6): each quartet distribution determines the induced unrooted quartet and its internal edge length, and the quartets determine the unrooted tree. For five taxa the numbers of unrooted gene trees sharing a probability separate the balanced, caterpillar and pseudocaterpillar rooted shapes, inequalities between the probabilities locate the root (Proposition 7), and the remaining edge lengths follow (Proposition 8). For more taxa the root is located on the edge $e$ of $\sigma^-$ such that every five-taxon subset whose induced tree contains $e$ has its root on $e$, and the edges at the root are measured on suitable five-taxon subsets. With one lineage per taxon no coalescence can occur on a pendant edge, so the distribution does not depend on pendant edge lengths; the abstract notes that the pendant length of a species with more than one sampled gene is identifiable.

## Depends on

- [The multispecies coalescent](../../multispecies-coalescent/gene-tree-prob.md)
- [The species quartet maximizes quartet support](../../multispecies-coalescent/split-01-most-probable.md)
- [An unrooted binary tree is determined by its quartets](../../../phylogenetics/splits-compatibility-ultrametrics-and-upgma/iso-of-displays-quartet-iff.md)

## Proof depends on

- [Gene trees restricted to a taxon subset follow the induced species tree](quartet-concordance-inside-larger-trees.md)

## Expansion

1. The four-taxon non-identifiability of the root (Proposition 3) with the explicit family of rooted trees.
2. The unrooted metric tree from quartet distributions and restriction to subsets (Lemma 5, Corollary 6).
3. The five-taxon case: gene tree probability classes for the three rooted shapes, location of the root, and the edges incident to the root (Propositions 7 and 8).
4. The general case by five-taxon subsets around each edge (Theorem 9), and the role of multiple samples per species for pendant edges.

## Sources

- E. S. Allman, J. H. Degnan and J. A. Rhodes, Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent, J. Math. Biol. 62 (2011; online 2010), 833–862, Proposition 3, Corollary 6, Propositions 7–8 and Theorem 9. <https://doi.org/10.1007/s00285-010-0355-7>
