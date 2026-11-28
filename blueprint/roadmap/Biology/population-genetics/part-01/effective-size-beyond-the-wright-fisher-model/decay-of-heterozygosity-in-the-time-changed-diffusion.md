# Decay of heterozygosity under a changing population size

Under the time-changed neutral Wright–Fisher diffusion $X_t = Y_{A(t)}$ with $A(t) = \int_0^t\nu(s)^{-1}ds$, the expected heterozygosity $H(x) = 2x(1 - x)$ satisfies $E[H(X_t)] = H(X_0)\exp(-A(t))$, since $L_0H = -H$; in generations, heterozygosity decays at rate $1/N(t)$ for $N(t)$ gene copies ($1/(2N(t))$ for $N(t)$ diploid individuals), so that over $T$ generations it is multiplied by $\exp(-\sum_t 1/N_t)$, the continuous counterpart of the exact discrete factor $\prod_t(1 - 1/N_t)$, which it bounds from above, the ratio of the two tending to $1$ when $\sum_t N_t^{-2} \to 0$, for diploid Wright–Fisher populations of fluctuating size, with $N_t = 2N_i$ gene copies for $N_i$ diploid individuals in generation $t$ ([effective size under fluctuating population size](../../effective-population-size/effective-size-under-fluctuating-population-size.md)); for constant size it is $(1 - 1/N)^r$ (Wright 1931). Higher moments $E[X_t^k(1 - X_t)^l]$ satisfy linear systems in $A(t)$; and the expected pairwise coalescence time of two genes under the variable-size coalescent gives the same decay, the probability that two genes have not coalesced by time $t$ being $\exp(-A(t))$ (Bhaskar and Song 2014, Sec. 2).

## Depends on

- [Effective population size under fluctuating population size](../../effective-population-size/effective-size-under-fluctuating-population-size.md)
- [Time-changed neutral diffusion under deterministic population-size change: construction and fixation](../../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/time-changed-neutral-diffusion-under-determinist.md)
- [Mass at infinity, density and mean of the pairwise coalescence time under a variable population size](../../../coalescent-theory/site-frequency-spectrum-under-variable-populatio/pair-coalescence-time-under-variable-size.md)

## Proof depends on

- [Mutation generator applied to heterozygosity](../../diffusion-theory/wright-fisher-diffusion-with-mutation/mutation-generator-heterozygosity.md)

## Expansion

1. The eigen-relation $L_0[x(1 - x)] = -x(1 - x)$ and the time-changed expectation.
2. Moment systems for higher polynomials under the time change.
3. Translation to generations and the product formula over generations.
4. The coalescent check: the [pairwise coalescence time under a variable population size](../../../coalescent-theory/site-frequency-spectrum-under-variable-populatio/pair-coalescence-time-under-variable-size.md), $P(T_2 > t) = e^{-A(t)}$, and moment duality.

## Sources

- S. Wright, Evolution in Mendelian populations, Genetics 16 (1931), 97–159. <https://doi.org/10.1093/genetics/16.2.97>
- A. Bhaskar and Y. S. Song, Descartes' rule of signs and the identifiability of population demographic models from genomic variation data, Ann. Statist. 42 (2014), 2469–2493. <https://arxiv.org/abs/1309.5056>
