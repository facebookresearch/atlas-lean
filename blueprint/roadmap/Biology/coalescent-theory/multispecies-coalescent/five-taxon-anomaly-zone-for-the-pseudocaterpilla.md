# The five-taxon pseudocaterpillar species tree has an anomaly zone

Let $T$ be a [species tree](species-tree.md) with the pseudocaterpillar topology $(((A, B), (C, D)), E)$ on five species and one lineage per species. Under the multispecies coalescent all lineages that reach the root population coalesce by [random joining](random-joining-real.md); when no coalescence happens below the root, the
labelled gene-tree topology therefore has its Yule probability $2^{n-1}/n! \cdot \prod_v (d_v - 1)^{-1}$, the product over internal nodes $v$ with $d_v$ descendant leaves. This labelled
topology has Yule probability $1/90$, less than the $1/60$ of each labelled balanced topology $(((A, B), C), (D, E))$. Make the internal branches of $T$ so short that the
probability of no coalescence below the root exceeds $1 - \varepsilon$, with $\varepsilon < (1/60 - 1/90)/(1/60 + 1) = 1/183$. Then, under the [multispecies coalescent](gene-tree-prob.md), the matching gene tree
has probability less than $\varepsilon + 1/90$ and the balanced topology $(((A, B), C), (D, E))$ more than $(1 - \varepsilon)/60$. So $T$ has an anomalous gene tree, although the balanced
[four-species tree](balanced-no-anomaly.md) has none.

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)

## Proof depends on

- [Random-joining probability as a fraction of ranked histories](random-joining-real.md)

## Related topics

- [No anomalous gene trees on the balanced four-species tree](balanced-no-anomaly.md)

## Sources

- J. H. Degnan and N. A. Rosenberg, "Discordance of species trees with their most likely gene trees", PLoS Genetics 2 (2006), e68, <https://doi.org/10.1371/journal.pgen.0020068>, Lemma 4 and its proof.
