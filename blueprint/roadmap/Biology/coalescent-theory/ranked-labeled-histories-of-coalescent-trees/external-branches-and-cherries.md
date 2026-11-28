# Cherry-count recursions and external branch length of the Kingman genealogy

In the rooted binary tree of Kingman's coalescent on $n \ge 3$ labelled leaves, the mean $n/3$ of the number of cherries (pairs of leaves that are each other's nearest relatives), and its variance $2n/45$ for $n > 6$, are stated in [Cherry distribution of ranked coalescent trees via a weighted generating function](cherries-and-pitchforks-of-ranked-coalescent-trees/cherry-generating-function-of-ranked-coalescent-trees.md); this page states the Yule-model recursions behind these moments, which give the variance $2n/45$ already for $n \ge 5$, and the expected external branch length. The topology of the Kingman tree is the Yule tree: Aldous (2001, Section 5.1) notes that the coalescent model, which repeatedly merges a uniformly chosen pair of lines of descent, and the Markov (Yule) model give the same distribution on cladograms. The following forward reading is this page's own argument: read forward from the root, the coalescent's random joining splits, at the step from $k - 1$ to $k$ lineages, a lineage chosen uniformly among the $k - 1$, because the merging pair is uniform among the $\binom k2$ pairs and the merged lineage is therefore uniform among the $k - 1$ lineages that remain. McKenzie and Steel (2000, Section 4.1, Theorem 2) state that under the Yule model, in which each pendant edge is equally likely to split, the mean $\mu_n$ and variance $\sigma_n^2$ of the number of cherries satisfy the recursions

$$\mu_{n+1} = 1 + \mu_n\Bigl(1 - \frac2n\Bigr), \qquad \sigma^2_{n+1} = \sigma^2_n\Bigl(1 - \frac4n\Bigr) + \frac{2\mu_n}{n}\Bigl(1 - \frac{2\mu_n}{n}\Bigr),$$

with solutions $\mu_n = n/3$ for $n \ge 3$ and $\sigma^2_n = 2n/45$ for $n \ge 5$; they also derive the asymptotic normality of the cherry count from an urn representation. Since only the topology enters, the same values hold for the time-changed coalescent of any deterministic population-size history. The [Cherry Count](../../not-yet-classified/cherry-distribution/cherry-count.md) page counts the cherries of an unrooted tree, a different object, and is not used here. The expected total length of the external branches, those ending at a leaf, is $2$ for every $n \ge 2$: it is the case $i = 1$ of the expected length $2/i$ of the branches subtending $i$ sample copies.

## Depends on

- [Expected block counts weighted by coalescence times sum to $2/i$](../../../Biology/coalescent-theory/expected-site-frequency-spectrum/sum-block-count-mul-inv-choose-two.md)

## Proof depends on

- [Random-joining law on block-size lists](../../../Biology/coalescent-theory/expected-site-frequency-spectrum/random-joining.md)

## Expansion

1. Cherries and external branches of a rooted binary tree, and the cherry count as a function of the topology.
2. The identification of the Kingman topology with the Yule model, by reading random joining forward from the root.
3. The recursions for the mean and variance of the cherry count under the Yule model and their solutions (Theorem 2 of McKenzie and Steel).
4. The expected external length $2$ and the per-leaf value $2/n$ by exchangeability.
5. The normal limit of the cherry count from the urn representation, as a separate statement.

## Sources

- A. McKenzie and M. Steel, Distributions of cherries for two models of trees, Math. Biosci. 164 (2000), 81–92, Section 4.1 and Theorem 2. <https://doi.org/10.1016/S0025-5564(99)00060-7>
- D. J. Aldous, Stochastic models and descriptive statistics for phylogenetic trees, from Yule to today, Statist. Sci. 16 (2001), Section 5.1. <https://doi.org/10.1214/ss/998929474>
