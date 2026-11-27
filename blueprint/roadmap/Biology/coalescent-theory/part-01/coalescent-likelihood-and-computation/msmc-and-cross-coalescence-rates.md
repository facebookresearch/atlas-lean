# Multiple sequentially Markov coalescent: first-coalescence hidden state

Schiffels and Durbin (2014) extend pairwise sequentially Markov inference to $M$ haplotypes by summarizing the genealogy at each position by the time to the first coalescence among the sampled sequences, together with the identities of the two sequences involved, and by the total length of the singleton branches; along the genome these hidden states follow approximate transition and emission rates derived from the SMC′ (their Results and Online Methods). Population size is a piecewise constant function of time estimated by maximum likelihood. The mean first coalescence time is $2/(M(M - 1))$ in units of $2N_0$ generations, so more haplotypes reach more recent times: two haplotypes resolve roughly 40 kya to 3 Mya, four 8 kya to 300 kya, and eight 2 kya to 50 kya in their simulations (Figure 2a). Within- and cross-population coalescence rates and the relative cross-coalescence rate, with its values near one before a split and zero after isolation, are stated in [MSMC2: pairwise composite likelihood under the sequentially Markovian coalescent](../../two-locus-coalescent/multiple-sequentially-markovian-coalescent/msmc2-pairwise-composite-likelihood.md), and their reading as a time-dependent migration model in the [time-dependent isolation–migration model fitted to coalescence rates](../../structured-coalescent/time-dependent-isolation-migration-fit-to-coalescence-rates.md). With the first-coalescence model, in simulated splits 10 kya and 100 kya, eight haplotypes recover the recent split better and four the older one, and migration after a split raises the estimated relative cross-coalescence rate (Figure 2b, Supplementary Figure 2c).

## Expansion

1. The first-coalescence hidden state for $M$ haplotypes, the singleton-branch emission, and the SMC′-based transitions.
2. The law of the first coalescence time and its mean $2/(M(M - 1))$.

## Sources

- S. Schiffels and R. Durbin, Inferring human population size and separation history from multiple genome sequences, Nat. Genet. 46 (2014), 919–925, Results (Figures 1–2) and Online Methods. <https://doi.org/10.1038/ng.3015>
