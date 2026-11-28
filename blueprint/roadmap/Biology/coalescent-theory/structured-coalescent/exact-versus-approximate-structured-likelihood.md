# Exact structured-coalescent likelihood and its approximations

For a genealogy whose tips are sampled in known demes, Beerli and Felsenstein (2001) write the probability density of a genealogy $\mathcal G$ that records every coalescence and every migration event as a product over the intervals between events: for each interval, the probability that neither a migration nor a coalescence occurs during it, an exponential of minus the total event rate times its length, times the rate of the event that ends it, a migration from one deme to another or a coalescence in a deme (their Equation 3); maximum-likelihood estimation then explores such genealogies by Markov chain Monte Carlo. Müller, Rasmussen and Stadler (2017) integrate over the migration histories instead. Their exact structured coalescent (ESCO) follows the probability of every configuration of lineage locations between events by ordinary differential equations, whose number is the number of demes raised to the number of coexisting lineages. The marginal lineage states approximation (MASCO) follows only the marginal location probabilities of each lineage, which reduces the number of equations to demes times lineages but ignores correlations between lineages, while still letting the coalescent process act on the lineage states: two lineages that do not coalesce for a long time become unlikely to share a deme. The state independence approximation (SISCO) assumes in addition that lineage states evolve independently of the coalescent process between events, so their probabilities change only by migration. In their simulations, SISCO overestimates the backward migration rate out of a deme with a faster coalescence rate, whereas MASCO does not; in the unequal-sampling experiment, the only one that also includes ESCO, SISCO is biased whereas ESCO and MASCO are not.

## Expansion

1. The structured coalescent with known tip locations, and the density of a genealogy with labelled migration events.
2. The configuration-state equations of the exact model and the resulting likelihood of a genealogy without migration events.
3. The marginal-states approximation and the dependence it discards (correlations between lineage locations).
4. The state-independence approximation and the additional dependence it discards (the effect of not coalescing on lineage locations), with the biases observed under asymmetric coalescence rates and unequal sampling.

## Sources

- P. Beerli and J. Felsenstein, Maximum likelihood estimation of a migration matrix and effective population sizes in n subpopulations by using a coalescent approach, Proc. Natl. Acad. Sci. USA 98 (2001), 4563–4568, Equation 3. <https://doi.org/10.1073/pnas.081068098>
- N. F. Müller, D. A. Rasmussen and T. Stadler, The structured coalescent and its approximations, Mol. Biol. Evol. 34 (2017), 2970–2981, Introduction and Results. <https://doi.org/10.1093/molbev/msx186>
