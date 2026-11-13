# Admixture-graph drift model

The admixture-graph drift model, stated at the level of second moments.

The allele frequency of population `X` is `root + ∑ e, weight X e * incr e` (see
`DriftModel.freq`), where `E` is the (finite) set of edges of the graph.

* `root` is the ancestral (root) allele frequency;
* `incr e` is the drift increment (frequency change) along edge `e`;
* `len e` is the drift length of edge `e`, i.e. the second moment `𝔼[incr e ^ 2]`;
* `weight X e` is the probability that a lineage sampled in `X` traverses `e`: on an
  admixture graph it is the sum, over root-to-`X` paths through `e`, of the product of the
  admixture proportions on the path; on a tree it is the `0`/`1` indicator that `e` lies on
  the root-to-`X` lineage.

f-statistics depend only on second moments of frequency differences, in which the root
cancels, so only these are assumed: the increments are square integrable, pairwise
uncorrelated (the mixed second moments `𝔼[incr e * incr f]`, `e ≠ f`, vanish, as they do for
independent mean-zero drift on distinct edges), and `𝔼[incr e ^ 2] = len e`.
