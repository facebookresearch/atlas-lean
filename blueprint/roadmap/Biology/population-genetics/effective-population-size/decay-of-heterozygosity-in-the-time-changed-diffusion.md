# Decay of heterozygosity under a changing population size

Under the time-changed neutral Wright–Fisher diffusion $X_t = Y_{A(t)}$ with $A(t) = \int_0^t\nu(s)^{-1}ds$, the expected heterozygosity $H(x) = 2x(1 - x)$ satisfies $E[H(X_t)] = H(X_0)\exp(-A(t))$, since $L_0H = -H$; in generations, heterozygosity decays at rate $1/N(t)$ for $N(t)$ gene copies ($1/(2N(t))$ for $N(t)$ diploid individuals), so that over $T$ generations it is multiplied by approximately $\exp(-\sum_t 1/N_t)$, the continuous counterpart of the exact discrete factor $\prod_t(1 - 1/N_t)$ for diploid Wright–Fisher populations of fluctuating size, with $N_t = 2N_i$ gene copies for $N_i$ diploid individuals in generation $t$ ([effective size under fluctuating population size](../../../Biology/population-genetics/effective-population-size/effective-size-under-fluctuating-population-size.md)); for constant size it is $(1 - 1/N)^r$ (Birkner, Lemma 1.1.1). Higher moments $E[X_t^k(1 - X_t)^l]$ satisfy linear systems in $A(t)$; and the expected pairwise coalescence time of two genes under the variable-size coalescent gives the same decay, the probability that two genes have not coalesced by time $t$ being $\exp(-A(t))$ (Bhaskar and Song 2014, Sec. 2).

## Depends on

- [Effective population size under fluctuating population size](../../../Biology/population-genetics/effective-population-size/effective-size-under-fluctuating-population-size.md)

## Expansion

1. The eigen-relation $L_0[x(1 - x)] = -x(1 - x)$ and the time-changed expectation.
2. Moment systems for higher polynomials under the time change.
3. Translation to generations and the product formula over generations.
4. The coalescent check: the [pairwise coalescence time under a variable population size](../../../Biology/coalescent-theory/site-frequency-spectrum-under-variable-populatio/pair-coalescence-time-under-variable-size.md), $P(T_2 > t) = e^{-A(t)}$, and moment duality.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Lemma 1.1.1.
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
