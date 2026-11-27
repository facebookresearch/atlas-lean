# Geometric steady state of short repeat lengths under two-way substitution

Let $P(L)$ be the genome-wide frequency of uninterrupted tandem repeat tracts of exactly $L$ copies of a motif $A$, and model the sequence as evolving under motif-unit substitutions alone, at rate $\mu$ for a non-motif unit $B$ turning into $A$ (lengthening) and rate $\nu$ for the reverse (shortening), with length-changing indels negligible. At stationarity each unit is independently $A$ with probability $p_A = \mu/(\mu+\nu)$ and $B$ with probability $p_B = \nu/(\mu+\nu)$, so a tract of $L$ consecutive $A$ units has frequency proportional to $p_A^{L}$:

$$P(L) \;\propto\; \left( \frac{\mu}{\mu+\nu} \right)^{L} \qquad (L \ll 10).$$

The short-repeat part of the distribution is therefore geometric, with the normalizing constant fixed by the mass of the shortest length class and the remaining mass carried by the long-repeat tail. The approximation holds up to the length at which the length-changing processes — expansion, contraction and non-motif insertion — stop being negligible relative to substitution, which for mononucleotide repeats is of order $L = 10$.

Above that length the dynamics decouple from substitution: the per-unit expansion, contraction and insertion rates grow with length, modelled as power laws $\epsilon_L = \epsilon_0 L^{\tau_\epsilon}$, $\kappa_L = \kappa_0 L^{\tau_\kappa}$ and $\iota_L = \iota_0 L^{\tau_\iota}$ for $L \ge 9$, and the steady state in that regime is governed by a continuum equation in which local expansion–contraction transitions compete with the non-local effects of repeat fission and fusion. A finite-length tail then requires contraction bias at large lengths, while expansion bias at intermediate lengths maintains it.

## Depends on

- [Stationary law of a finite birth–death chain](../../../../Probability/markov-chains/birth-death-processes/stationary-law-of-a-finite-birth-death-chain.md)

## Expansion

The derivation of the geometric law is a statement about random strings: when the only moves are independent per-unit substitutions between two states, the stationary measure is a product measure, and the probability of sampling a run of $L$ successive $A$ units is $p_A^{L}$ (times the boundary factor that normalizes over tract starts, absorbed into the constant). The empirical significance is that the entire short-repeat regime is explained with no selection and no slippage: the observed genome-wide distribution of repeat lengths, which is stable across hundreds of mammalian genomes over evolutionary time, is consistent with mutation alone, provided the length-dependent instability rates switch from expansion-biased to contraction-biased as length grows. That transition also defines the onset length at which a repeat becomes an independently evolving genomic element, namely where expansion and contraction rates overtake the substitution rate; the posterior over the instability parameters inferred by approximate Bayesian computation from the human distribution is informative about exactly this onset length.

## Sources

- R. J. McGinty, D. J. Balick, S. M. Mirkin, S. R. Sunyaev, "Inherent instability of simple DNA repeats shapes an evolutionarily stable distribution of repeat lengths", *Nature Communications* 16 (2025), <https://doi.org/10.1038/s41467-025-66725-5> (PMC12769509). Results and Methods, "Analytic modeling of repeat length dynamics", short-repeat regime, Equation (8), and long-repeat regime.
