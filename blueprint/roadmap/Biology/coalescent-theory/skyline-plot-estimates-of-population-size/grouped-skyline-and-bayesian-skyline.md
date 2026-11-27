# Classical, generalized and heterochronous skyline estimates

For a known genealogy whose intercoalescent intervals $u_k$ carry $k$ lineages, the piecewise demographic model takes the effective size constant on each interval, $N_e(t) = \theta_k$ for $t_k < t \le t_{k-1}$; the resulting likelihood factorizes over intervals, the intervals are independent, and estimating each $\theta_k$ amounts to estimating the rate of an exponential distribution from a single draw, with maximum likelihood estimates $\hat\theta_k = \binom k2 u_k$, the classical skyline plot (Minin, Bloomquist and Suchard 2008, equations (2) and (3), after Pybus et al. 2000). These estimates have high variance from overfitting. The generalized skyline plot of Strimmer and Pybus groups intervals: intervals shorter than a threshold $\epsilon$ borrow the size of a neighbouring interval, with $\epsilon$ chosen by a second-order extension of the corrected Akaike criterion. The Bayesian skyline plot of Drummond et al. (2005), a Bayesian extension of this grouping, is the separate [Bayesian skyline coalescent prior](bayesian-skyline-coalescent-prior.md). For serially sampled genealogies, sampling events split intervals into subintervals that contribute survival factors without a coalescence, and the classical skyline estimate extends accordingly (Minin, Bloomquist and Suchard 2008, equations (4) and (5)). If interval lengths are measured in another unit, $u_k^* = cu_k$, the same likelihood recovers the rescaled trajectory $cN_e(t)$.

## Depends on

- [Classic skyline estimate of population size](../../../Biology/coalescent-theory/skyline-plot-estimates-of-population-size/skyline-estimate.md)
- [Log-likelihood of one coalescent interval in the skyline model](../../../Biology/coalescent-theory/skyline-plot-estimates-of-population-size/skyline-log-lik.md)

## Expansion

1. The grouped likelihood: for a segment of consecutive intervals with a common size, the event count and exposure $\sum \binom{k}{2} u_k$, and the segment maximum likelihood estimate.
2. The generalized skyline grouping rule with threshold $\epsilon$ and its selection criterion.
3. The heterochronous extension with sampling subintervals.

## Sources

- V. N. Minin, E. W. Bloomquist and M. A. Suchard, Smooth skyride through a rough skyline: Bayesian coalescent-based inference of population dynamics, Mol. Biol. Evol. 25 (2008), 1459–1471, sections "Piecewise demographic model for isochronous data" and "Piecewise demographic model for heterochronous data", equations (2)–(5). <https://doi.org/10.1093/molbev/msn090>
- Original result: A. J. Drummond, A. Rambaut, B. Shapiro and O. G. Pybus, Bayesian coalescent inference of past population dynamics from molecular sequences, Mol. Biol. Evol. 22 (2005), 1185–1192. <https://doi.org/10.1093/molbev/msi103>
