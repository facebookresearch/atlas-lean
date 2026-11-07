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
- [Normalization](gene-tree-prob-true.md)
- [Total gene-tree probability is one](gene-tree-prob-eq-one.md)
- [Nonnegativity of the exit law](exit-law-nonneg.md)
- [Gene-tree probabilities are nonnegative](gene-tree-prob-nonneg.md)

## Evaluating random-joining expectations

- [Expectation under random joining as an average over histories](integral-random-joining.md)
- [Rational-valued expectation under random joining](integral-random-joining-rat-cast.md)
- [Random-joining probability as a fraction of ranked histories](random-joining-real.md)
- [Additivity of the exit law](exit-law-add.md)
- [Additivity](gene-tree-prob-or.md)
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
- [Probability of the discordant three-species gene tree with cherry {0, 2}](gene-tree-prob-triple-cherry-02.md)
- [Probability of the discordant three-species gene tree with cherry {1, 2}](gene-tree-prob-triple-cherry-12.md)
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
- [The boundary `a(x)` of the anomaly zone](dr-f-lt-dr-h-iff.md)
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
