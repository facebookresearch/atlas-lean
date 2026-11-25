# Monte Carlo phylogenetic bootstrap support

Fix a tree estimator $\mathrm{est}$ (a map from alignments of $m$ sites on a taxon set $X$ to trees on $X$), an alignment $M$ with columns $M_1,\dots,M_m$, and a split $\sigma$ of $X$. A bootstrap replicate is an alignment $M^*=(M_{J_1},\dots,M_{J_m})$ whose column indices $J_1,\dots,J_m$ are drawn independently and uniformly from $\{1,\dots,m\}$, that is, columns resampled with replacement from the empirical column law. With $B$ independent replicates $M^{*1},\dots,M^{*B}$, the **Monte Carlo bootstrap support** of $\sigma$ is

$$\widehat s_B(\sigma)=\frac1B\sum_{b=1}^B\bigl[\sigma\text{ is a split of }\mathrm{est}(M^{*b})\bigr].$$

Conditionally on $M$, it is an unbiased Monte Carlo estimate of the ideal support $s(\sigma)=P^*\bigl(\sigma\text{ is a split of }\mathrm{est}(M^*)\bigr)$, the fraction of the $m^m$ resamplings whose estimated tree contains $\sigma$ (the [bootstrap support](../splits-compatibility-ultrametrics-and-upgma/bootstrap-support.md) of the split), and $\widehat s_B(\sigma)\to s(\sigma)$ almost surely as $B\to\infty$. The limit $s(\sigma)$ is a conditional probability given the observed alignment; without further assumptions it is neither a p-value for a hypothesis about $\sigma$ nor a posterior probability of $\sigma$. Resampling single columns treats sites as independent and ignores linkage among sites.

For a one-column alignment ($m=1$) every replicate equals $M$, so $\widehat s_B(\sigma)=s(\sigma)\in\{0,1\}$ for every $B$.

## Depends on

- [Bootstrap support](../splits-compatibility-ultrametrics-and-upgma/bootstrap-support.md)
- [The Monte Carlo estimator is consistent](../../../ComputerScience/machine-learning/bayesian-inference-and-sampling/monte-carlo-and-importance-sampling/tendsto-mc-estimate.md)

## Expansion

A full page must establish:

- the identification of the ideal support $s(\sigma)$ with the exact count over all $m^m$ resampling maps, for estimators that return unrooted trees with their splits;
- the almost sure limit $B\to\infty$ from the strong law applied to the independent indicators;
- the one-column example;
- a precise form of the non-p-value caveat, with an explicit example in which $s(\sigma)$ is not a valid p-value for the hypothesis that $\sigma$ is a split of the true tree; this, and a block-bootstrap variant for linked sites, remain open obligations.

## Sources

- J. Felsenstein, *Confidence limits on phylogenies: an approach using the bootstrap*, Evolution 39 (1985), 783–791 (phylogenetic bootstrap).
