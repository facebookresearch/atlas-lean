# Limits of the invariance of fixation probabilities

The invariance of fixation probabilities under subdivision rests on the drift of the census-weighted frequency being a constant multiple of its quadratic-variation rate, which needs conservative migration, genic selection with the same coefficient in every deme, and a connected migration graph. Each failure of an assumption breaks the identity in an explicit model.

1. Non-conservative migration. In two neutral demes of equal size with backward migration rates $q_{12} = a$ and $q_{21} = b$, the left null vector of $Q$ is $w \propto (b, a)$, so an allele fixed in deme $1$ and absent from deme $2$ fixes everywhere with probability $b/(a + b)$, not the census average $\frac12$ unless $a = b$, the conservative case.
2. Dominance. With genotype fitnesses giving the local drift $\alpha x_i(1 - x_i)(h + (1 - 2h)x_i)$, the drift of $\bar x$ is $\alpha\sum_iw_ix_i(1 - x_i)(h + (1 - 2h)x_i)$ while its quadratic-variation rate stays $\sum_iw_ix_i(1 - x_i)/K$; their ratio depends on the spread of frequencies among demes unless $h = \frac12$, and no function of $\bar x$ alone is then a martingale in general. Whitlock (2003, abstract) finds that with arbitrary dominance and arbitrary deme contributions the fixation probability is strongly affected by structure, approximately $2hs(1 - F_{ST})N_e/N_{tot}$ for a new beneficial allele, with $F_{ST}$ a weighted version of Wright's measure.
3. Spatially varying selection. If the coefficient $\alpha_i$ differs among demes, the drift of $\bar x$ is $\sum_i\alpha_iw_ix_i(1 - x_i)$, again not proportional to the quadratic-variation rate.
4. Disconnected demes. Each connected component is absorbed separately, and the population can end with the allele fixed in some components and lost in others.
5. Fixation times. Even when the probability is invariant, the time is not: the random clock of the total frequency runs at most at the panmictic rate, so the mean absorption time is at least the panmictic one; Whitlock (2003, abstract) reports that structure strongly affects the expected time to fixation or loss.

## Depends on

- [Invariance of fixation probabilities under conservative migration](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/maruyama-fixation-invariance.md)
- [Neutral fixation probability in a structured population](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/neutral-fixation-with-reproductive-weights.md)
- [A random clock for the total allele frequency in a structured population](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/maruyama-stochastic-clock.md)

## Expansion

1. The two-deme non-conservative example with its reproductive-value weights.
2. A two-deme example with dominance in which the fixation probability differs from the panmictic formula, computed numerically or by perturbation in $h - \frac12$.
3. A two-deme example with opposite selection in the two demes.
4. The disconnected case and the comparison of fixation times.

## Sources

- M. C. Whitlock, Fixation probability and time in subdivided populations, Genetics 164 (2003), 767–779, abstract. <https://doi.org/10.1093/genetics/164.2.767>
