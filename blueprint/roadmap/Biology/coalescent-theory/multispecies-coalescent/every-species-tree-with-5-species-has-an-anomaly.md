# Every species tree with at least five species has an anomaly zone

Every rooted binary species-tree topology on $n \ge 5$ species, with one lineage per species, has branch lengths for which, under the [multispecies coalescent](gene-tree-prob.md),
some gene-tree topology is strictly more probable than the one matching the species tree. With three species there are no anomalous gene trees, and with
four species the caterpillar has an [anomaly zone](caterpillar-exists-anomalous-iff.md) while the balanced tree [has none](balanced-no-anomaly.md). The proof of Degnan and Rosenberg has three parts:

1. A topology that is not the most probable labelled topology under the Yule model produces anomalies, by making all internal branches short, as for the
   [caterpillar](five-taxon-anomaly-zone-for-the-caterpillar-shap.md) and [pseudocaterpillar](five-taxon-anomaly-zone-for-the-pseudocaterpilla.md) five-taxon trees.
2. The most probable topologies for $n = 5, 6, 7, 8$ produce anomalies by explicit choices of short and long branches, as for the [balanced five-taxon tree](five-taxon-anomaly-zone-for-the-balanced-shape.md).
3. For $n \ge 9$, a most probable topology has a subtree below the root with between $5$ and $n - 1$ species, which produces anomalies by induction; an
   [anomalous root subtree](extension-lemma-anomaly-persists-when-adding-a-t.md) then makes the whole tree anomalous.

## Depends on

- [The multispecies coalescent](gene-tree-prob.md)

## Proof depends on

- [The five-taxon caterpillar species tree has an anomaly zone](five-taxon-anomaly-zone-for-the-caterpillar-shap.md)
- [The five-taxon pseudocaterpillar species tree has an anomaly zone](five-taxon-anomaly-zone-for-the-pseudocaterpilla.md)
- [The five-taxon balanced species tree has an anomaly zone](five-taxon-anomaly-zone-for-the-balanced-shape.md)
- [An anomalous root subtree makes the whole species tree anomalous](extension-lemma-anomaly-persists-when-adding-a-t.md)

## Expansion

Part 1 for general $n$ (the argument of the caterpillar and balanced pages, with the general Yule formula) and the cases $n = 6, 7, 8$ of part 2, whose
anomalous gene trees are $(((A, B), C), (D, (E, F)))$-type topologies built as in the source's Figure 3b–d, are stated in the source and not reproduced as separate
pages; the record's route through the three five-taxon shapes and a general extension lemma is replaced by the source's route.

## Sources

- J. H. Degnan and N. A. Rosenberg, "Discordance of species trees with their most likely gene trees", PLoS Genetics 2 (2006), e68, <https://doi.org/10.1371/journal.pgen.0020068>, Proposition 2, Definition 3, Lemmas 4 and 5.
