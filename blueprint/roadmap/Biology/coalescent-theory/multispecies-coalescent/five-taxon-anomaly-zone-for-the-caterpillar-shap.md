# The five-taxon caterpillar species tree has an anomaly zone

Let $T$ be a [species tree](species-tree.md) with the caterpillar topology $((((A, B), C), D), E)$ on five species and one lineage per species. Under the multispecies coalescent all lineages that reach the root population coalesce by [random joining](random-joining-real.md); when no coalescence happens below the root, the
labelled gene-tree topology therefore has its Yule probability $2^{n-1}/n! \cdot \prod_v (d_v - 1)^{-1}$, the product over internal nodes $v$ with $d_v$ descendant leaves. For five
taxa the Yule probabilities are $1/180$ for each labelled caterpillar, $1/60$ for each labelled balanced topology $(((A, B), C), (D, E))$ and $1/90$ for each labelled pseudocaterpillar
$(((A, B), (C, D)), E)$; with $60$, $30$ and $15$ labellings these sum to $1$. Make the three internal branches of $T$ so short that the probability of no coalescence below the root exceeds $1 - \varepsilon$, with
$\varepsilon < (1/60 - 1/180)/(1/60 + 1) = 2/183$. Then, under the [multispecies coalescent](gene-tree-prob.md), the gene tree matching $T$ has probability less than $\varepsilon + 1/180$, while the balanced topology
$(((A, B), C), (D, E))$ has probability greater than $(1 - \varepsilon)/60$, which is larger. So $T$ has an anomalous gene tree for these branch lengths.

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)

## Proof depends on

- [Random-joining probability as a fraction of ranked histories](random-joining-real.md)

## Related topics

- [The four-species anomaly zone](caterpillar-exists-anomalous-iff.md)

## Sources

- J. H. Degnan and N. A. Rosenberg, "Discordance of species trees with their most likely gene trees", PLoS Genetics 2 (2006), e68, <https://doi.org/10.1371/journal.pgen.0020068>, Lemma 4 and its proof.
