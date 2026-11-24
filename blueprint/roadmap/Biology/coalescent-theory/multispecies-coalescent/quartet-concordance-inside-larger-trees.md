# Quartet concordance inside larger species trees

Let $\sigma^+$ be a rooted metric species tree on a taxon set $X$, with internal edge lengths in coalescent units, and consider the multispecies coalescent with one lineage sampled per taxon. Allman, Degnan and Rhodes (2011, Lemma 5) show that for every subset $S \subseteq X$ the distribution of the gene tree restricted to $S$ is the multispecies coalescent distribution of the species tree $\sigma^+(S)$ induced on $S$: summing the gene tree probabilities on $X$ over all gene trees whose restriction to $S$ is a given tree gives that tree's probability on $\sigma^+(S)$, where an edge of $\sigma^+(S)$ has as length the sum of the lengths of the edges of $\sigma^+$ that it replaces. For four taxa (their Section 4.1), on the balanced tree $((a, b){:}x, (c, d){:}y)$ the unrooted gene tree $AB|CD$ has probability $1 - \frac23 e^{-(x + y)}$ and each of $AC|BD$ and $AD|BC$ has probability $\frac13 e^{-(x + y)}$, and on the caterpillar $(((a, b){:}x, c){:}y, d)$ the same holds with $x + y$ replaced by $x$; in both cases the exponent is the internal edge length of the unrooted quartet. Combining the two, for every four-taxon set $q \subseteq X$ the unrooted gene tree on $q$ agrees with the quartet induced by the species tree with probability $1 - \frac23 e^{-t_q}$, and each of the other two quartets has probability $\frac13 e^{-t_q}$, where $t_q$ is the length of the internal edge of the unrooted quartet induced on $q$, the sum of the species-tree edge lengths along the path separating the two pairs.

## Depends on

- [No anomalous unrooted quartets, balanced species tree](../../../Biology/coalescent-theory/multispecies-coalescent/gene-tree-prob-balanced-split-01.md)
- [Probability of quartet split 02|13 on the balanced tree](../../../Biology/coalescent-theory/multispecies-coalescent/gene-tree-prob-balanced-split-02.md)
- [No anomalous unrooted quartets, caterpillar species tree](../../../Biology/coalescent-theory/multispecies-coalescent/gene-tree-prob-caterpillar-split-01.md)
- [Probability of quartet split 02|13 on the caterpillar tree](../../../Biology/coalescent-theory/multispecies-coalescent/gene-tree-prob-caterpillar-split-02.md)

## Expansion

1. Restriction of a rooted metric species tree to a subset of taxa, with the lengths of merged edges added.
2. The marginalization identity of Lemma 5, from the description of the multispecies coalescent population by population.
3. The four-taxon unrooted probabilities on the balanced and caterpillar shapes (Section 4.1).
4. The quartet statement for arbitrary labels: identification of $t_q$ as the length of the internal edge of the induced unrooted quartet, whichever of the two rooted shapes is induced.

## Sources

- E. S. Allman, J. H. Degnan and J. A. Rhodes, Identifying the rooted species tree from the distribution of unrooted gene trees under the coalescent, J. Math. Biol. 62 (2011; online 2010), 833–862, Section 4.1 and Lemma 5. <https://doi.org/10.1007/s00285-010-0355-7>
