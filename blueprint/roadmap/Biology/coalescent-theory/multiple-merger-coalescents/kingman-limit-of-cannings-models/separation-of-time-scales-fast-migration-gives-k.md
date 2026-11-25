# Fast migration gives Kingman's coalescent with an effective population size

Consider a structured population of demes with relative sizes $c_i > 0$, in which migration acts on a faster time scale than coalescence. Suppose the sampled lineages migrate independently on the fast time scale, each by the same irreducible aperiodic chain on demes with stationary law $p$. Then the fast chain on the deme labels of all sampled lineages has the product stationary law $p \otimes \dots \otimes p$, and its transition matrix $A$ satisfies $A^m \to P$. Then, by [Möhle's lemma on Markov chains with two time scales](../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md), the sample genealogy with deme labels collapsed converges to Kingman's coalescent with pair coalescence rate

$$\sum_i \frac{p_i^2}{c_i},$$

the size-weighted collision rate under the product law. Without independence of the lineages' migration, the joint stationary law need not be a product, and the rate is the expectation of $1/c_i$ on the event that two lineages share deme $i$ under that joint law. The deme labels themselves converge only in the averaged sense. Periodic fast chains, such as deterministic alternation between two demes, are excluded.

## Depends on

- [Möhle's lemma on Markov chains with two time scales](../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md)

## Proof depends on

- [Structured coalescent for n lineages with a general migration matrix](../../structured-coalescent/structured-coalescent-for-n-lineages-with-a-gene.md)
- [Under Möhle–Sagitov, transition matrices converge to Kingman's](tendsto-ancestral-matrix-pow.md)

## Expansion

1. The collapse of the deme labels and the pair rate, from the two-time-scale lemma applied to the joint chain.
2. Checks: for relative sizes $c = (1, 2)$ and $p = (1/2, 1/2)$ the rate is $3/8$, not $1/2$. For the symmetric island model with $d$ demes of size $N$ and fast migration, the effective size is $N_e = dN$.
3. The excluded cases: the identity fast chain, and periodic two-deme alternation, under which lineages in different demes never meet.

## Sources

- M. Nordborg and S. M. Krone, Separation of time scales and convergence to the coalescent in structured populations, in *Modern Developments in Theoretical Population Genetics*, Oxford University Press (2002) (separation of time scales).
- M. Möhle, A convergence theorem for Markov chains arising in population genetics and the coalescent with selfing, *Adv. Appl. Probab.* 30 (1998), 493–512 (convergence theorem).
