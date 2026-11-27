# Invariance of the neutral clock under uniform turnover or local birth-death balance

Use the replacement model of [site fixation probabilities](site-fixation-probabilities-and-the-neutral-substitution-rate.md): replacement probabilities $e_{ij}$, birth rates $b_i = \sum_j e_{ij}$, death rates $d_i = \sum_j e_{ji}$, site fixation probabilities $\rho_i$ and substitution rate $K = (Nu/B)\sum_i d_i\rho_i$.

**Proposition (uniform turnover).** If $d_i$ is the same for all sites, then $\rho = 1/N$ and $K = u$, whatever the birth rates.

**Proposition (local balance).** The following are equivalent:

1. $b_i = d_i$ for every site $i$;
2. $\rho_i = 1/N$ for every site $i$.

In either case $\rho = 1/N$ and $K = u$. In particular, symmetric dispersal $e_{ij} = e_{ji}$ implies $K = u$.

## Depends on

- [Site fixation probabilities and the neutral substitution rate](site-fixation-probabilities-and-the-neutral-substitution-rate.md)

## Expansion

If $d_i = B/N$ for all $i$, then $\rho = \frac1B\sum_i \frac BN\rho_i = \frac1N\sum_i\rho_i = \frac1N$. For local balance, substituting $\rho_i = 1/N$ into $d_i\rho_i = \sum_j e_{ij}\rho_j$ gives $d_i/N = b_i/N$, so (2) implies (1); conversely, if $b_i = d_i$ then the uniform vector solves the balance equations and is normalized, so by uniqueness it is the solution. With $\rho_i = 1/N$ the formula for $\rho$ again gives $1/N$. Symmetric dispersal forces $b_i = \sum_j e_{ij} = \sum_j e_{ji} = d_i$. Local balance can also be read as a corollary of the circulation theorem of evolutionary graph theory. Most earlier models of neutral drift in structured populations satisfy one of these two hypotheses, which is why spatial effects on the neutral clock went unnoticed.

## Sources

- B. Allen, C. Sample, Y. Dementieva, R. C. Medeiros, C. Paoletti and M. A. Nowak, "The molecular clock of neutral evolution can be accelerated or slowed by asymmetric spatial structure", PLoS Computational Biology 11 (2015), e1004108, Results 1 and 2 and Methods, <https://doi.org/10.1371/journal.pcbi.1004108>, PMCID PMC4342344.
