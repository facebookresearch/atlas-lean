# Multispecies coalescent

## Species trees

- [Rooted binary species tree with branch lengths](species-tree.md)
- [Species tree with nonnegative branch lengths](nonneg-lengths.md)
- [Species below a node of a species tree](taxa.md)
- [Clusters of a species tree](clusters.md)
- [Topology of a species tree](shape.md)

## Tavaré's probabilities sum to one

- [Tavaré's probabilities sum to one](sum-tavare-prob.md)
- [Tavaré's probabilities are nonnegative](tavare-prob-nonneg.md)

## Coalescence inside one population

- [Lineages after the first coalescence events of a ranked history](merge-along.md)
- [Merging lineages from singletons gives the ancestral blocks](merge-along-singletons.md)
- [Clusters formed along a ranked history](clades-along.md)

## The multispecies coalescent

- [Coalescence along one branch of the species tree](branch-step.md)
- [Law of the lineages leaving a species-tree branch](exit-law.md)
- [The multispecies coalescent](gene-tree-prob.md)
- [Root branch length does not affect gene-tree probabilities](gene-tree-prob-node-length.md)
- [Exit law of a constant continuation](exit-law-eq-const.md)
- [Normalization of gene-tree probabilities](gene-tree-prob-true.md)
- [Total gene-tree probability is one](gene-tree-prob-eq-one.md)
- [Nonnegativity of the exit law](exit-law-nonneg.md)
- [Gene-tree probabilities are nonnegative](gene-tree-prob-nonneg.md)

## Evaluating random-joining expectations

- [Expectation under random joining as an average over histories](integral-random-joining.md)
- [Rational-valued expectation under random joining](integral-random-joining-rat-cast.md)
- [Random-joining probability as a fraction of ranked histories](random-joining-real.md)
- [Additivity of the exit law](exit-law-add.md)
- [Additivity of gene-tree probabilities](gene-tree-prob-or.md)
- [Gene-tree probabilities are at most one](gene-tree-prob-le-one.md)

## Tavaré's formula for two and three lineages

- [Two lineages remain distinct with probability $e^{-t}$](tavare-prob-two-two.md)
- [Two lineages coalesce with probability $1 - e^{-t}$](tavare-prob-two-one.md)
- [Three lineages remain distinct with probability $e^{-3t}$](tavare-prob-three-three.md)
- [Three lineages have two ancestors at time $t$](tavare-prob-three-two.md)
- [Three lineages have one ancestor at time $t$](tavare-prob-three-one.md)

## Three species

- [Three-species tree ((0, 1), 2)](triple.md)
- [Three-gene tree with a given cherry](triple-tree.md)
- [Clusters of the three-species tree](clusters-triple.md)
- [Three-species concordance](gene-tree-prob-triple-matching.md)
- [Probability of the discordant three-species gene tree with cherry $\{0, 2\}$](gene-tree-prob-triple-cherry-02.md)
- [Probability of the discordant three-species gene tree with cherry $\{1, 2\}$](gene-tree-prob-triple-cherry-12.md)
- [No anomalous gene trees for three species](triple-no-anomaly.md)
- [Wright–Fisher limit of the no-coalescence probability](tendsto-no-coal-prob-pow-floor-two.md)

## Four species: the anomaly zone

- [Caterpillar four-species tree](caterpillar.md)
- [Balanced four-species tree](balanced.md)
- [Caterpillar four-gene tree](caterpillar-tree.md)
- [Balanced four-gene tree](balanced-tree.md)
- [Clusters of the caterpillar species tree](clusters-caterpillar.md)
- [Degnan–Rosenberg probability of the matching caterpillar gene tree](dr-f.md)
- [Degnan–Rosenberg formula g for the gene tree ((A, C), (B, D))](dr-g.md)
- [Degnan–Rosenberg formula h for the gene tree ((A, B), (C, D))](dr-h.md)
- [The matching gene tree](gene-tree-prob-caterpillar-matching.md)
- [Probability of the gene tree ((A, C), (B, D)) on the caterpillar](gene-tree-prob-caterpillar-ac-bd.md)
- [Probability of the gene tree ((A, D), (B, C)) on the caterpillar](gene-tree-prob-caterpillar-ad-bc.md)
- [Probability of the gene tree ((A, B), (C, D)) on the caterpillar](gene-tree-prob-caterpillar-ab-cd.md)
- [Boundary of the four-species anomaly zone](anomaly-a.md)
- [Boundary for three anomalous gene trees](anomaly-b.md)
- [$g(x, y) < h(x, y)$ for a positive shallower branch](dr-g-lt-dr-h.md)
- [The boundary $a(x)$ of the anomaly zone](dr-f-lt-dr-h-iff.md)
- [Degnan–Rosenberg criterion: $f(x, y) < g(x, y)$ iff $y < b(x)$](dr-f-lt-dr-g-iff.md)
- [Value $\log(7/6)$ of the three-anomaly boundary at zero](anomaly-b-zero.md)
- [Three-anomaly boundary is maximal at zero](anomaly-b-le-anomaly-b-zero.md)
- [Anomaly-zone boundary blows up for short deep branches](tendsto-anomaly-a.md)
- [Anomalous gene tree on four species](caterpillar-anomalous-iff.md)
- [Anomaly of ((A, C), (B, D)) and ((A, D), (B, C)) on the caterpillar](caterpillar-anomalous-ac-bd-iff.md)
- [Balanced gene tree on four genes](is-balanced-gene-tree.md)
- [Only balanced gene trees can be anomalous on the caterpillar](caterpillar-le-matching.md)
- [$g(x, y) \le h(x, y)$ for a nonnegative shallower branch](dr-g-le-dr-h.md)
- [The four-species anomaly zone](caterpillar-exists-anomalous-iff.md)
- [No anomalous gene trees on the balanced four-species tree](balanced-no-anomaly.md)

## Five or more species: anomaly zones

- [The five-taxon caterpillar species tree has an anomaly zone](five-taxon-anomaly-zone-for-the-caterpillar-shap.md)
- [The five-taxon pseudocaterpillar species tree has an anomaly zone](five-taxon-anomaly-zone-for-the-pseudocaterpilla.md)
- [The five-taxon balanced species tree has an anomaly zone](five-taxon-anomaly-zone-for-the-balanced-shape.md)
- [An anomalous root subtree makes the whole species tree anomalous](extension-lemma-anomaly-persists-when-adding-a-t.md)
- [Every species tree with at least five species has an anomaly zone](every-species-tree-with-5-species-has-an-anomaly.md)

## Unrooted quartets

- [Gene tree displaying a quartet split](displays-split.md)
- [No anomalous unrooted quartets, caterpillar species tree](gene-tree-prob-caterpillar-split-01.md)
- [Probability of quartet split 02|13 on the caterpillar tree](gene-tree-prob-caterpillar-split-02.md)
- [Probability of quartet split 03|12 on the caterpillar tree](gene-tree-prob-caterpillar-split-03.md)
- [No anomalous unrooted quartets, balanced species tree](gene-tree-prob-balanced-split-01.md)
- [Probability of quartet split 02|13 on the balanced tree](gene-tree-prob-balanced-split-02.md)
- [Probability of quartet split 03|12 on the balanced tree](gene-tree-prob-balanced-split-03.md)
- [The species quartet maximizes quartet support](split-01-most-probable.md)

## Clade probabilities under random joining

- [Clade of a ranked history](is-clade.md)
- [Clade probability](random-joining-is-clade.md)
- [Clade probability under random joining for at most five genes](random-joining-is-clade-of-le-five.md)

- [The multispecies coalescent as a constructed process](msc-realization-gene-tree-probability-equals-the.md)
- [Identifiability of networks under the network multispecies coalescent](network-coalescent-identifiability-questions-spe.md)
- [Network multispecies coalescent: the gene-tree probability kernel of a fixed network](network-multispecies-coalescent-fixed-network-ge.md)
- [One species-tree branch: exit law and merge order of the realized coalescent](one-species-tree-branch-exit-law-and-merge-order.md)
- [Gene tree density under the multispecies coalescent with branch population functions](gene-tree-density-under-the-multispecies-coalescent-with-branch-population-functions.md)
- [Hierarchical Bayesian posterior for species trees from multilocus data](hierarchical-bayesian-posterior-for-species-trees-from-multilocus-data.md)
- [Hard and soft anomalous networks under the network multispecies coalescent](anomalous-networks-under-correlated-inheritance.md)
- [Concordance-factor signatures of cycles in level-1 quartet networks](big-cycle-property-detects-4-cycles.md)
- [Identifiability of level-1 networks from orderings of quartet concordance factors](level-1-network-identifiability-from-quartet-concordance-factor-orderings.md)
- [Numerical parameter identifiability on a level-1 network from quartet CFs](level-1-numerical-parameter-identifiability.md)
- [Topological identifiability of a level-1 species network from quartet CFs](level-1-topological-identifiability-from-quartet-cfs.md)
- [Two-cycles of a level-1 network are not identifiable from quartet CFs](level-1-two-cycles-not-identifiable.md)
- [Quartet concordance factors do not depend on the root of a network](quartet-cfs-independent-of-the-root.md)
- [Quartet concordance factors depend only on the unrooted quartet network](quartet-concordance-factors-depend-only-on-the-unrooted-quartet-network.md)
- [Three-cycles with a two-leaf hybrid are the source of four-taxon anomalies](three-two-cycles-and-four-taxon-anomalies.md)
- [A degree-2 sub-blob can be replaced by a single edge without changing quartet CFs](two-sub-blob-replacement-preserves-quartet-cfs.md)
## Networks: the tree of blobs
- [Tree of blobs of a species network under the coalescent](tree-of-blobs-identifiability/README.md)
- [Species tree estimation under taxon deletion](species-tree-estimation-under-taxon-deletion/README.md)
