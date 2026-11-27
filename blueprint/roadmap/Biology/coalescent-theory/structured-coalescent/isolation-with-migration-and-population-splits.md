# Isolation with migration: piecewise structured histories and gene-tree likelihoods

In an isolation-with-migration model, two populations descend from a panmictic ancestral population that split at some time in the past, and after the split they may or may not exchange migrants. Nielsen and Wakeley (2001, Abstract) estimate, by Markov chain Monte Carlo in a Bayesian or a likelihood framework, the migration rate into each population, the time since divergence, and the sizes of the two current populations relative to the ancestral one, and find that even a single nonrecombining locus has substantial power to test for no ongoing migration or for symmetric migration. Backward in time, sampled lineages follow a structured coalescent in the two populations until the split and then a single coalescent in the ancestral population (for two lineages, the [two-lineage isolation-with-migration law across a population split](isolation-and-isolation-with-migration-two-linea.md)), so the history is piecewise: each epoch has its own sizes and migration rates, and lineages are relabelled at the epoch boundary. Within an epoch the density of a genealogy with labelled migration events is the product, over the intervals between events, of the probability of no event in the interval and the rate of the event that ends it (Beerli and Felsenstein 2001, Equation 3); across the split the epoch densities multiply, with all surviving lineages moved into the ancestral population. The likelihood of a gene tree with branch lengths is the integral of this density over the migration histories compatible with it, which is what Markov chain Monte Carlo over migration histories approximates.

## Depends on

- [Transition rates of the two-lineage structured coalescent](../../../Biology/coalescent-theory/structured-coalescent/rate.md)

## Expansion

1. The piecewise history: epochs with population sizes and migration rates, and the relabelling of lineages at a split.
2. The structured coalescent within an epoch for $n$ lineages and the density of a genealogy with labelled migration events.
3. The composition of epoch densities across the split.
4. The gene-tree likelihood as an integral over migration histories, and its approximation by Markov chain Monte Carlo.
5. Tests of no migration and of symmetric migration from one or several loci, as separate statements.

## Sources

- R. Nielsen and J. Wakeley, Distinguishing migration from isolation: a Markov chain Monte Carlo approach, Genetics 158 (2001), 885–896, Abstract. <https://doi.org/10.1093/genetics/158.2.885>
- P. Beerli and J. Felsenstein, Maximum likelihood estimation of a migration matrix and effective population sizes in n subpopulations by using a coalescent approach, Proc. Natl. Acad. Sci. USA 98 (2001), 4563–4568, Equation 3. <https://doi.org/10.1073/pnas.081068098>
