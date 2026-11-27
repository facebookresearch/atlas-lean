# Heaps-law criterion for open pan-genomes

Consider an infinite sequence of genomes of a species and the expected [pan-genome curve](pan-and-core-genome-size-curves.md) $P(k)$, the expected number of gene families in the first $k$ genomes, with increments $\Delta(k) = P(k) - P(k-1) \ge 0$, the expected number of new families contributed by the $k$-th genome. The pan-genome is **closed** if $P(k)$ is bounded and **open** otherwise. Suppose the new-family counts follow a Heaps-type power law

$$\Delta(k) = \kappa\, k^{-\alpha}, \qquad \kappa > 0,\ \alpha \in \mathbb{R}.$$

**Proposition.**

1. The pan-genome is closed if and only if $\alpha > 1$, in which case $P(k)$ converges to a finite limit.
2. If $\alpha < 1$, then $P(k) \sim \frac{\kappa}{1-\alpha}\, k^{1-\alpha}$, a power law with exponent $\gamma = 1 - \alpha \in (0, \infty)$; if $\alpha = 1$, $P(k) \sim \kappa \ln k$.
3. Consequently a pan-genome curve fitted as a power law $P(k) \approx A k^{\gamma} + C$ with $A > 0$ and $\gamma > 0$ indicates an open pan-genome, while a curve approaching a plateau indicates a closed one.

## Depends on

- [Pan-genome and core-genome size curves](pan-and-core-genome-size-curves.md)

## Proof sketch

$P(k) = P(0) + \kappa \sum_{j=1}^k j^{-\alpha}$, and the $p$-series $\sum j^{-\alpha}$ converges exactly when $\alpha > 1$; comparison with $\int_1^k x^{-\alpha} dx$ gives the growth rates in part 2. The criterion is due to Tettelin and coauthors, who imported Heaps' law on vocabulary growth from text statistics. In practice, pipelines such as BPGA fit an empirical power-law regression to the median pan-genome curve and an exponential decay to the core-genome curve, the latter's asymptote estimating the size of the core genome of the species; the extrapolated curves are then read as open or nearly closed. A finite sample cannot distinguish a slowly growing open pan-genome from a large closed one, so the conclusion rests on the extrapolation model.

## Sources

- N. M. Chaudhari, V. K. Gupta and C. Dutta, "BPGA: an ultra-fast pan-genome analysis pipeline", Scientific Reports 6 (2016) 24373, Methods ("Pan-genome profile analysis": power-law fit to the pan-genome curve, exponential fit to the core-genome curve) and Results ("Pan-genome profile estimation and statistics"), <https://doi.org/10.1038/srep24373>, PMCID PMC4829868.
- H. Tettelin, D. Riley, C. Cattuto and D. Medini, "Comparative genomics: the bacterial pan-genome", Current Opinion in Microbiology 11 (2008) 472–477 (Heaps' law formulation of open and closed pan-genomes).
