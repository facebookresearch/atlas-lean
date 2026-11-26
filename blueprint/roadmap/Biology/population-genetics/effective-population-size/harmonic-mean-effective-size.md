# The harmonic-mean effective size

For a neutral Wright–Fisher population whose size is $\nu(t)$ times a reference size, with $\nu$ continuous and positive, the diffusion is the reference-size diffusion $Y$ run on the clock $A(t) = \int_0^t\nu(s)^{-1}ds$, $X_t = Y_{A(t)}$. If $\nu$ is periodic with period $T_0$, then $A(kT_0) = kT_0/\nu_H$ for every integer $k \ge 0$, where $\nu_H = T_0/\int_0^{T_0}\nu(s)^{-1}ds$ is the harmonic mean of $\nu$ over a period. Hence the frequency observed at the ends of whole cycles has exactly the law of the constant-size diffusion with relative size $\nu_H$ observed at the same times: $(X_{kT_0})_{k \ge 0}$ and $(Y_{kT_0/\nu_H})_{k \ge 0}$ have the same law, whatever the period. This is the diffusion counterpart of the harmonic-mean effective size of Wright (1938), which arises because $1 - F$ is multiplied by $1 - 1/(2N_i)$ in generation $i$ and these factors are averaged (Crow and Kimura 1970); over $n$ generations the harmonic mean $n/\sum_i N_i^{-1}$ is at most the arithmetic mean and at most $n \min_i N_i$, so it is governed by the smallest sizes. The identification is exact only through the clock: statistics that depend on when events happen within a cycle, or on a history that is not repeated, such as a single recent bottleneck, are not those of the constant-size diffusion with the harmonic-mean size in general. For genealogies, Sjödin et al. (2005) likewise find a harmonic-mean effective size only when the size fluctuations are fast compared with coalescence, and none when they occur on the coalescent time scale.

## Depends on

- [Effective population size under fluctuating population size](../../../Biology/population-genetics/effective-population-size/effective-size-under-fluctuating-population-size.md)
- [Time-changed neutral diffusion under deterministic population-size change: construction and fixation](../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/time-changed-neutral-diffusion-under-determinist.md)
- [Decay of heterozygosity under a changing population size](../../../Biology/population-genetics/effective-population-size/decay-of-heterozygosity-in-the-time-changed-diffusion.md)

## Expansion

1. The clock at cycle ends, $A(kT_0) = kT_0/\nu_H$, and equality in law at cycle ends.
2. Statistics preserved (laws at cycle ends, long-run decay rates of heterozygosity) and statistics not preserved (timing within a cycle).
3. The comparison with the discrete product formula and its harmonic-mean approximation.

## Sources

- S. Wright, Size of population and breeding structure in relation to evolution, Science 87 (1938), 430–431.
- J. F. Crow and M. Kimura, *An Introduction to Population Genetics Theory*, Harper & Row, New York, 1970, the effective number of a population whose size changes between generations.
- I. Kaj and S. M. Krone, The coalescent process in a population with stochastically varying size, J. Appl. Probab. 40 (2003), 33–48. The genealogical counterpart of the clock: Kingman's coalescent run on a time change given by an additive functional of the size process.
- P. Sjödin, I. Kaj, S. Krone, M. Lascoux and M. Nordborg, On the meaning and existence of an effective population size, Genetics 169 (2005), 1061–1070, section on fluctuating population size. <https://doi.org/10.1534/genetics.104.026799>
