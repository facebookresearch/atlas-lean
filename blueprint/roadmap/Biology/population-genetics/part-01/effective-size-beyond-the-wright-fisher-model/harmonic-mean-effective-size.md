# Harmonic-mean clock of a periodically varying population size

For a neutral Wright–Fisher population whose size is $\nu(t)$ times a reference size, with $\nu$ continuous and positive, the diffusion is the reference-size diffusion $Y$ run on the clock $A(t) = \int_0^t\nu(s)^{-1}ds$, $X_t = Y_{A(t)}$. If $\nu$ is periodic with period $T_0$, then $A(kT_0) = kT_0/\nu_H$ for every integer $k \ge 0$, where $\nu_H = T_0/\int_0^{T_0}\nu(s)^{-1}ds$ is the harmonic mean of $\nu$ over a period: at the ends of whole cycles the clock is that of a constant relative size $\nu_H$. This is the diffusion form of the harmonic-mean effective size of Wright (1938). Over $n$ generations of sizes $N_1, \dots, N_n$ the harmonic mean $n/\sum_i N_i^{-1}$ is at most the arithmetic mean and at most $n \min_i N_i$, so it is governed by the smallest sizes. The genealogical counterpart for randomly fluctuating sizes, where fast fluctuations average to the stationary harmonic mean and fluctuations on the coalescent time scale give no effective size, is the [coalescent effective size under random population-size fluctuations](../../effective-population-size/coalescent-effective-size-under-random-population-size-fluctuations.md).

## Depends on

- [Effective population size under fluctuating population size](../../effective-population-size/effective-size-under-fluctuating-population-size.md)
- [Time-changed neutral diffusion under deterministic population-size change: construction and fixation](../../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/time-changed-neutral-diffusion-under-determinist.md)
- [Decay of heterozygosity under a changing population size](decay-of-heterozygosity-in-the-time-changed-diffusion.md)

## Expansion

1. The clock at cycle ends, $A(kT_0) = kT_0/\nu_H$, for periodic $\nu$.
2. Separate target: the cycle-end equality in law of $(X_{kT_0})_{k \ge 0}$ and $(Y_{kT_0/\nu_H})_{k \ge 0}$ for every period, from $X = Y \circ A$ and item 1, with the statistics it preserves (laws at cycle ends, long-run decay rates of heterozygosity) and those it does not preserve in general (timing within a cycle, or a history that is not repeated, such as a single recent bottleneck).
3. The comparison with the discrete-generation harmonic mean $n/\sum_i N_i^{-1}$.

## Sources

- S. Wright, Size of population and breeding structure in relation to evolution, Science 87 (1938), 430–431.
