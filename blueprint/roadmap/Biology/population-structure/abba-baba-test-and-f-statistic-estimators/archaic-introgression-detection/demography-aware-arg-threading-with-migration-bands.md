# Demography-aware ARG threading with migration bands

**Demographic model.** Fix a population model with present-day populations that merge backwards in time into a single panmictic ancestor by the oldest of $k$ discrete time points $0 = t_0 < t_1 < \dots < t_{k-1}$, with a population size for each population in each time interval. A **migration band** is an instantaneous event at a fixed time, from a source population into a recipient population, with prior probability $p_M$: a lineage in the recipient population that reaches the band (backwards in time) moves to the source population with probability $p_M$ and stays with probability $1 - p_M$.

**Population paths.** For a lineage that starts in a known present-day population, its **population path** is the sequence of populations it occupies over its time span; it is determined by the population tree and by which migration bands it follows. Let $P$ be the maximum number of population paths available to any lineage.

**Threading HMM.** ARGweaver samples ancestral recombination graphs by MCMC: one sample's branch is removed from every local tree ("unthreading") and re-inserted by sampling from a hidden Markov model along the $L$ sites ("threading"). In the demography-aware version, a hidden state at a site is a triple (branch of the local tree, discrete coalescence time, population path), restricted to triples in which the new lineage and the branch it joins are in the same population at the coalescence time. Coalescence states reached through a migration band receive prior weight $p_M$ for each band followed and $1 - p_M$ for each band passed without migrating, in addition to the coalescent and recombination terms of the discretized sequentially Markov coalescent. Each threading step costs

$$O\big(L\,n\,k^2\,P^2\big)$$

for $n$ samples, compared with $O(Lnk^2)$ without population structure; restricting the model to at most one migration event per site keeps $P$ small and makes the size of an unsampled (ghost) source population irrelevant, since at most one lineage occupies it.

**Posterior introgression probability.** For sampled ARGs $G^{(1)}, \dots, G^{(M)}$ from the chain, the posterior probability that a haploid genome is introgressed through band $b$ at site $s$ is estimated by the fraction of samples whose local tree at $s$ routes that genome's ancestral lineage through $b$; a site is called introgressed when this fraction is at least $1/2$.

## Remarks

Without migration and with known population labels, the state space is a subset of the panmictic one, because a lineage can only join branches present in its own population at that time, so the algorithm is faster than the panmictic sampler. Each migration band a lineage may follow can double the number of candidate population paths above that time, and a coalescence point may become reachable by several paths, so the HMM must carry the path explicitly; transition probabilities between states at adjacent sites factor into a recombination step (which may change branch, time and path) and a re-coalescence step whose rates depend on the population sizes along the new path, giving the $P^2$ factor. Because the MCMC targets the posterior over ARGs given the data and the demographic model, averaging indicators over sampled ARGs is a Monte Carlo estimate of the posterior probability of introgression, and it distinguishes heterozygous from homozygous introgression in a diploid by counting how many of its two lineages follow the band.

## Sources

- M. J. Hubisz, A. L. Williams and A. Siepel, "Mapping gene flow between ancient hominins through demography-aware inference of the ancestral recombination graph", *PLoS Genetics* 16 (2020), e1008895, Results "ARGweaver-D can sample ARGs conditional on an arbitrary demographic model" and Materials and methods "Demographic model", "Efficiency of the algorithm" and "Calling introgressed regions", <https://doi.org/10.1371/journal.pgen.1008895> (PMC7410169).
