# Pairwise differences under Poisson mutation

## Ancestral partitions as lists of blocks

- [Block partition of the sample with gene positions](is-block-partition.md)
- [Position of a block after two blocks merge](merge-idx.md)
- [Merging shortens a block list by one if the removed position exists](length-merge-blocks.md)
- [Entries of the list after merging two blocks](get-elem-merge-blocks.md)
- [Merging two blocks of a block partition gives a block partition](is-block-partition-merge-blocks.md)
- [Smaller label of a pair of lineages](pair-lo.md)
- [Larger label of a pair of lineages](pair-hi.md)
- [Smaller and larger labels of $\{u, v\}$ are its minimum and maximum](pair-lo-pair-hi-of-map.md)
- [The two labels of a pair of $k$ lineages are distinct and below $k$](pair-lo-pair-hi-spec.md)
- [Each coalescence event merges the two blocks of the pair it records](blocks-after-succ.md)
- [The blocks after $t$ events depend only on the first $t$ steps](blocks-after-congr.md)
- [The $n - t$ blocks after $t \le n - 1$ events form a block partition](blocks-after-spec.md)

## When two sampled genes coalesce

- [Genes apart after $t$ events: no lineage block contains them all](pair-apart.md)
- [Two genes are apart exactly when their block positions differ](pair-apart-iff.md)
- [Genes are together after a step iff together before or merged by it](pair-apart-succ-iff.md)
- [A pair apart after the next event was already apart](of-succ.md)

## Counting histories

- [Double counting when exactly one value of a coordinate leaves a set](card-filter-mul-add-of-exists-unique.md)
- [Counting the histories that merge two apart genes at step $t$](card-pair-apart-succ.md)
- [Two distinct genes are apart before any coalescence event](pair-apart-zero.md)
- [Fraction of histories in which two genes are apart after $t$ events](card-pair-apart-div.md)

## The branches between two sampled genes

- [Sampled genes below a branch of the genealogy](branch-block.md)
- [Branches separating two sampled genes](pair-path.md)
- [Branches shared by two sampled genes](pair-shared.md)
- [Coalescence time of two sampled genes](pair-coal-time.md)
- [Two branches per epoch separate a pair while apart, none afterwards](card-pair-path-epoch.md)
- [One shared branch per epoch once a pair has coalesced, none before](card-pair-shared-epoch.md)
- [The separating path has length twice the apart epochs' positive parts](sum-pair-path-branch-length.md)

## Poisson mutation marking with an arbitrary topology

- [Poisson mutation kernel on a Kingman genealogy with topology](kingman-tree-mutation-kernel.md)
- [Pairwise differences as mutations on the separating branches](pair-diff.md)
- [The Poisson mean of a branch is measurable in the genealogy](measurable-branch-mean.md)
- [Each branch count is conditionally Poisson given the genealogy](has-cond-distrib-branch-of-tree-mutation.md)
- [The pairwise difference count is integrable under Poisson mutation](integrable-pair-diff-of-mutation.md)
- [Conditional mean of the pairwise differences given the genealogy](cond-exp-pair-diff-of-mutation.md)
- [Expected differences of a pair are θ times its mean coalescence time](integral-pair-diff-of-mutation.md)
- [Tajima's E π = θ under Poisson mutation, given Exp(1) pair times](integral-mean-pair-diff-of-mutation.md)

## A concrete model: exponential epochs and random joining

- [Probability that a pair is apart with k lineages under random joining](integral-pair-apart-random-joining.md)
- [Law of the Kingman genealogy with random-joining topology](kingman-genealogy-measure.md)
- [Coalescence time is a measurable function of the genealogy](measurable-pair-coal-time.md)
- [Mean coalescence time of a pair in the Kingman genealogy is one](integral-pair-coal-time-kingman-genealog.md)
- [Marked Kingman model with random-joining topology](kingman-tree-mutation-measure.md)
- [Genealogy coordinate of the marked model follows the genealogy law](measure-preserving-genealogy.md)
- [Holding times of the marked Kingman model with topology](of-tree-mutation-model.md)
- [Epoch vector of the marked model is its genealogy's epoch coordinate](epochs-of-tree-mutation-model.md)
- [Conditional law of the counts given the genealogy in the marked model](has-cond-distrib-kingman-tree-mutation-m.md)
- [Expected pairwise differences of one pair in the marked Kingman model](integral-pair-diff-kingman-tree-mutation.md)
- [Tajima's E π = θ in the marked Kingman model with random joining](integral-mean-pair-diff-kingman-tree-mut.md)

## The law of the coalescence time of a pair

- [Ratio $(m - 1)/(m + 1)$ of the pair separation probability](pair-ratio.md)
- [Mixing hypoexponential transforms over the epoch of coalescence](sum-pair-ratio-prod.md)
- [Epoch sum above a threshold with $P(M \le k) = p_{n,k}$ is Exp(1)](has-law-sum-ite-of-threshold.md)
- [After $n - 1$ coalescence events any two genes share a lineage](not-pair-apart-sub-one.md)
- [Coalescence time of a pair in the Kingman genealogy is Exp(1)](has-law-pair-coal-time-kingman-genealogy.md)
- [Coalescence time of a pair in the marked Kingman model is Exp(1)](has-law-pair-coal-time-kingman-tree-muta.md)

## Second moments of pairwise differences

- [Overlap length of the paths of two pairs of genes](pair-path-overlap.md)
- [The mutation kernel at a genealogy is a product of Poisson laws](kingman-tree-mutation-kernel-apply.md)
- [Product moment of two pairwise differences given the genealogy](integral-pair-diff-mul-kernel.md)
- [Product of two pairwise differences is integrable in the marked model](integrable-pair-diff-mul-kingman-tree-mu.md)
- [Product moment of two pairwise differences in the marked Kingman model](integral-pair-diff-mul-kingman-tree-muta.md)
- [Covariance of two pairwise differences in the marked Kingman model](covariance-pair-diff-kingman-tree-mutati.md)
- [Variance of the differences of one pair in the marked Kingman model](variance-pair-diff-kingman-tree-mutation.md)

## Distinct pairs: backward recursions over histories

- [Coalescence rate after $u$ coalescence events](rate-after.md)
- [Indicator that a set of genes is apart after $u$ events](apart-ind.md)
- [Functions of the first $t$ steps of a history](depends-before.md)
- [Changing a step $j \ge u$ keeps apartness after $u$ events](pair-apart-update-of-le.md)
- [Replacing one step by every pair of lineages in a sum over histories](sum-mul-card-eq-sum-update.md)
- [Weighted sums over a state reached by $m$ choices of step $t$](sum-mul-ite-mul-rate-after.md)
- [Apartness of two genes after step $t$ is replaced by a given pair](pair-apart-update-succ-iff.md)
- [Counting the pairs of lineages whose sorted labels lie in a set](card-lineage-pair-mem.md)
- [Counting the pairs of lineages whose sorted labels avoid a set](card-lineage-pair-not-mem.md)
- [All but one choice of step $t$ keep an apart pair apart](card-update-pair-apart-succ.md)
- [Probability that an apart pair stays apart at the next step](sum-mul-apart-ind-succ.md)
- [Two genes apart after $u$ events are apart after any $t \le u$ events](pair-apart-of-le.md)

## Remaining coalescence times given the history

- [Conditional mean of the remaining coalescence time given the history](future-mean.md)
- [Variance part of the remaining product moment of two coalescence times](future-diag.md)
- [Conditional product moment of the remaining coalescence times](future-prod.md)
- [The mean remaining time of a pair vanishes once it has coalesced](apart-ind-mul-future-mean.md)
- [The remaining coalescence time of a pair still apart has mean one](sum-mul-future-mean.md)
- [The remaining coalescence time of an apart pair has second moment two](sum-mul-future-prod-self.md)

## Three distinct lineages: two pairs sharing a gene

- [Two genes in one lineage after $t$ events stay together afterwards](not-pair-apart-of-le.md)
- [After $b$ and $c$ merge, $a$ is apart from both or from neither](pair-apart-congr-of-not.md)
- [Three genes in three distinct lineages after $t$ events](apart3.md)
- [Gene $a$ apart from $b$ and $c$, which share a lineage](split-a.md)
- [All but three choices of step $t$ keep three distinct lineages apart](card-update-apart3-succ.md)
- [A single choice of step $t$ merges $b$ with $c$ while $a$ stays apart](card-update-split-a-succ.md)
- [Remaining product moment $4/3$ from three distinct lineages](sum-mul-apart3-future-prod.md)

## Four distinct lineages: two disjoint pairs

- [Four genes in four distinct lineages after $t$ events](apart4.md)
- [Genes in distinct lineages stay apart unless step $t$ joins them](pair-apart-succ-iff-sorted.md)
- [Coordinates for the next step from four distinct lineages](apart4-succ-iff.md)
- [Apartness after replacing step $t$, for genes in distinct lineages](pair-apart-update-succ-iff-sorted.md)
- [All but six choices of step $t$ keep four distinct lineages apart](card-update-apart4-succ.md)
- [Exactly one choice of step $t$ merges two genes that are apart](card-update-and-not-pair-apart-succ.md)
- [Indicator decomposition of the next state from four distinct lineages](ite-apart4-mul-apart-ind-succ.md)
- [Merging $a$ with $c$ from four lineages leaves $a$, $b$, $d$ apart](apart3-of-apart4-not-ac.md)
- [Remaining product moment $11/9$ from four distinct lineages](sum-mul-apart4-future-prod.md)

## Overlap of the paths of two pairs

- [Number of lineages of an epoch that separate both of two pairs](overlap-count.md)
- [Expected remaining overlap of two paths given the history](future-overlap.md)
- [The overlap count in terms of the lineage labels of the genes](overlap-count-eq.md)
- [Overlap of two paths through a shared gene](overlap-count-shared.md)
- [No lineage separates both of two pairs whose four genes are apart](overlap-count-of-apart4.md)
- [No lineage separates both pairs once the first pair has coalesced](overlap-count-of-not-left.md)
- [The overlap count depends only on the lineages of the four genes](overlap-count-congr.md)
- [Genes that have coalesced share their lineage label from then on](pos-eq-of-not-pair-apart.md)
- [Mean remaining path overlap of two pairs from four distinct lineages](sum-mul-apart4-future-overlap.md)

## From histories to the Kingman genealogy

- [Product moment of two coalescence times given the history](integral-pair-coal-time-mul-pi-measure.md)
- [Expected overlap of two paths given the history](integral-pair-path-overlap-pi-measure.md)
- [Product moment of two coalescence times as an average over histories](integral-pair-coal-time-mul-eq-sum.md)
- [Expected overlap of two paths as an average over histories](integral-pair-path-overlap-eq-sum.md)

## Moments for two pairs sharing a gene

- [Product moment of the coalescence times of two pairs sharing a gene](integral-pair-coal-time-mul-shared.md)
- [Covariance of the coalescence times of two pairs sharing a gene](covariance-pair-coal-time-shared.md)
- [Mean overlap of the paths of two pairs sharing a gene](integral-pair-path-overlap-shared.md)
- [Covariance of the pairwise differences of two pairs sharing a gene](covariance-pair-diff-shared.md)

## Moments for two disjoint pairs

- [Product moment of the coalescence times of two disjoint pairs](integral-pair-coal-time-mul-disjoint.md)
- [Covariance of the coalescence times of two disjoint pairs](covariance-pair-coal-time-disjoint.md)
- [Mean overlap of the paths of two disjoint pairs](integral-pair-path-overlap-disjoint.md)
- [Covariance of the pairwise differences of two disjoint pairs](covariance-pair-diff-disjoint.md)

- [Candidate and visible local-tree changes along the chromosome](candidate-vs-visible-local-tree-changes-expected.md)
- [Finitely many breakpoints and a jointly measurable local-tree field](finitely-many-breakpoints-and-a-jointly-measurab.md)
- [General Markov mutation along branches and the law of sample types](general-markov-mutation-along-branches-and-sampl.md)
- [Marked whole-chromosome ARG on [0,1) with homogeneous recombination: construction](marked-whole-chromosome-arg-on-0-1-with-homogene.md)
