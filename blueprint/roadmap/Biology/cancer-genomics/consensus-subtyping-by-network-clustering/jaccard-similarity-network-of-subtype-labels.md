# Jaccard-similarity network of subtype labels

Let $\mathcal{P}$ be a set of samples and let $\mathcal{C} = \{S_1,\dots,S_K\}$ be the union of the subtype classes produced by several independent classification systems applied to $\mathcal{P}$, each $S_k \subseteq \mathcal{P}$ being the set of samples assigned to that class. The subtype association network has vertex set $\mathcal{C}$ and weighted edges

$$w(S_k, S_l) = J(S_k, S_l) = \frac{|S_k \cap S_l|}{|S_k \cup S_l|} \in [0,1], \qquad k \ne l,$$

retained only for pairs whose overlap is significant: for each pair, the $p$-value of the hypergeometric test for over-representation of $S_k$ within $S_l$ is computed and adjusted for multiple testing, and the edge is kept when the adjusted $p$-value falls below a fixed threshold. Classes from the same classification system are disjoint, so their Jaccard index is $0$ and no within-system edge survives.

## Depends on

- [Hypergeometric over-representation test](../../bioinformatics/functional-scores-enrichment-and-networks/gene-category-over-representation/hypergeometric-over-representation-test.md)
- [Hypergeometric distribution](../../../Probability/distributions/discrete/hypergeometric-distribution/hypergeometric.md)

## Remarks

The Jaccard index is a metric complement ($1 - J$ is a metric on finite sets), it is invariant to the overall sample size, and it penalizes a class that is much larger than its partner, which is the behaviour wanted when comparing classification systems of different granularity. Significance filtering is a second, independent requirement: a pair can have moderate Jaccard index purely because both classes are large, and the hypergeometric test, which is the exact null distribution for sampling the labels of one class without replacement from the population, removes those pairs. What remains is a graph whose connected structure reflects agreement between systems rather than their individual partitions.

## Sources

- Guinney J, Dienstmann R, Wang X, et al. The consensus molecular subtypes of colorectal cancer. *Nature Medicine* 21:1350-1356 (2015), Online Methods, network construction. DOI <https://doi.org/10.1038/nm.3967>. PMCID PMC4636487.
