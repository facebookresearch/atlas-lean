# Consistency of Bayesian triplet inference of species trees from site patterns

**Data and model.** Coalescent independent sites (CIS) are aligned sites, each with its own gene tree drawn independently under the multispecies coalescent on a clock-like species tree $(S, \boldsymbol\tau)$, followed by Jukes-Cantor (JC69) substitution along that gene tree. For a subset of three (or four) taxa, each site is reduced to its JC69 site-pattern class (for three taxa, $XXX$, $XXY$, $XYX$, $YXX$, $XYZ$), since under JC69 only the pattern of equalities matters. The data are the counts $\mathbf{d} = (d_k)$ of these patterns over $J$ sites, and the likelihood is multinomial,

$$
L\big((S, \boldsymbol\tau)\mid\mathbf{d}\big) \propto \prod_k \big[\delta_k\mid(S, \boldsymbol\tau)\big]^{d_k},
$$

where $\delta_k\mid(S,\boldsymbol\tau)$ is the site-pattern probability obtained by integrating the JC69 pattern probabilities over coalescent gene trees, available in closed form for four taxa, with the three-taxon case obtained by marginalizing out one taxon.

**Posterior over topologies.** With exponential priors on the divergence times that keep the integral analytic (for three taxa, $\tau_2 \sim \mathrm{Exp}(\beta)$ and $\tau_1 \mid \tau_2 \sim \mathrm{U}(0, \tau_2)$) and a Yule prior on rooted topologies (uniform over the three rooted triplets), Bayes' theorem gives

$$
P(S = s\mid\mathbf{d}) = \frac{L(s\mid\mathbf{d})\,P(S = s)}{\sum_{i=1}^3 L(S_i\mid\mathbf{d})\,P(S = S_i)}, \qquad L(s\mid\mathbf{d}) \propto \prod_k\big[\delta_k\mid s\big]^{d_k}, \quad \delta_k\mid s = \int \delta_k\mid(s, \boldsymbol\tau)\,f(\boldsymbol\tau)\,\mathrm{d}\boldsymbol\tau .
$$

For four taxa the sum runs over the $15$ rooted topologies, and each unrooted quartet collects the five rooted trees compatible with it.

**Theorem (consistency for triplets).** For CIS data on three taxa under the multispecies coalescent with JC69 and a molecular clock, let $\hat S$ be the maximum a posteriori rooted triplet. Then $\mathbb{P}(\hat S = S) \to 1$ as the number of sites $J \to \infty$, for any prior under which $0 < \tau_1 < \tau_2$ with probability $1$.

**Corollary (whole tree).** With a Bonferroni adjustment over the $\binom{n}{3}$ triplets, for $J$ large enough all MAP triplets are simultaneously correct with probability at least $1 - \varepsilon$, and the $n$-taxon rooted species tree is then determined by its triplets (a rooted tree is recovered from its compatible rooted triples).

## Expansion

As $J \to \infty$ the empirical pattern frequencies converge to the true probabilities $\delta_k\mid(S, \boldsymbol\tau)$, and the log-posterior of each topology, divided by $J$, converges to the negative cross-entropy between the true pattern distribution and the prior-averaged pattern distribution of that topology. Under the multispecies coalescent with a clock, the pattern whose singleton taxon is the outgroup (for $((a,b),c)$ the pattern $XXY$ with $a, b$ equal) is strictly more probable than the two other $XXY$-type patterns, which are equal to each other. Averaging over any prior with $\tau_1 < \tau_2$ preserves this ordering, so the true topology has strictly the largest limiting score and wins with probability tending to $1$. Weighting quartets or triplets by their posterior probabilities and assembling them (weighted triplet or quartet methods) gives fast species-tree estimates that inherit this consistency. For unrooted quartets, consistency is supported by simulation but not proven.

## Depends on

- [Rooted binary species tree with branch lengths](../../../../coalescent-theory/multispecies-coalescent/species-tree.md)
- [Jukes–Cantor transition probability](../../../jukes-cantor-model/jc-prob.md)

## Proof depends on

- [Strong law for pairwise independent columns with a common law](../../../consistency-of-minimum-distance-gtr-estimators/ae-tendsto-empirical-freq.md)
- [A rooted binary tree is determined by its triplets](../../../splits-compatibility-ultrametrics-and-upgma/eq-of-displays-triplet-iff.md)

## Sources

- Andrew Richards and Laura Kubatko, "Bayesian Weighted Triplet and Quartet Methods for Species Tree Inference", arXiv (2020), Section 2 (Definitions 1–2), Section 3 (site-pattern likelihood, priors and posterior over topologies, Theorem 3.1), Appendix (three-taxon site-pattern probabilities), <https://doi.org/10.48550/arXiv.2010.06063>.
- J. Chifman and L. Kubatko, "Identifiability of the unrooted species tree topology under the coalescent model with time-reversible substitution processes, site-specific rate variation, and invariable sites", Journal of Theoretical Biology 374 (2015), 35–47, <https://doi.org/10.1016/j.jtbi.2015.03.006>.
