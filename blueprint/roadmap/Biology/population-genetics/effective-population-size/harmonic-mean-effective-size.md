# The harmonic-mean effective size

For a neutral Wright–Fisher population whose size is $\nu(t)$ times a reference size, the diffusion is the reference-size diffusion $Y$ run on the clock $A(t) = \int_0^t\nu(s)^{-1}ds$, $X_t = Y_{A(t)}$. If $\nu$ is periodic with period $T_0$, then $A(kT_0) = kT_0/\nu_H$ for every integer $k \ge 0$, where $\nu_H = T_0/\int_0^{T_0}\nu(s)^{-1}ds$ is the harmonic mean of $\nu$ over a period. Hence the frequency observed at the ends of whole cycles has exactly the law of the constant-size diffusion with relative size $\nu_H$ observed at the same times: $(X_{kT_0})_{k \ge 0}$ and $(Y_{kT_0/\nu_H})_{k \ge 0}$ have the same law, whatever the period. Between cycle ends the two differ by at most the variation of $A(t) - t/\nu_H$ over one period, and if the period is shrunk, $\nu(t) = \nu_1(t/\varepsilon)$, then $A(t) \to t/\nu_H$ uniformly on compact time intervals and $X$ converges pathwise, uniformly on compacts, to $Y_{\cdot/\nu_H}$ by continuity of the paths of $Y$. This is the diffusion counterpart of the harmonic mean of Felsenstein (Section VI.7, equation (VI-44)), which arises because $1 - F$ is multiplied by $1 - 1/(2N_i)$ in generation $i$ and these factors are averaged; over $n$ generations the harmonic mean $n/\sum_i N_i^{-1}$ is at most the arithmetic mean and at most $n \min_i N_i$, so it is governed by the smallest sizes. The identification is exact only through the clock: statistics that depend on when events happen within a cycle, or on a history that is not repeated, such as a single recent bottleneck, are not those of the constant-size diffusion with the harmonic-mean size in general.

## Depends on

- [Effective population size under fluctuating population size](../../../Biology/population-genetics/effective-population-size/effective-size-under-fluctuating-population-size.md)
- [Deterministic time change for a changing population size](../../../Biology/population-genetics/effective-population-size/diffusion-time-change-for-a-changing-population-size.md)
- [Decay of heterozygosity under a changing population size](../../../Biology/population-genetics/effective-population-size/decay-of-heterozygosity-in-the-time-changed-diffusion.md)

## Expansion

1. The clock at cycle ends, $A(kT_0) = kT_0/\nu_H$, and equality in law at cycle ends.
2. The bound on $A(t) - t/\nu_H$ within a cycle, and pathwise convergence as the period shrinks.
3. Statistics preserved (laws at cycle ends, long-run decay rates of heterozygosity) and statistics not preserved (timing within a cycle).
4. The comparison with the discrete product formula and its harmonic-mean approximation.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics*, course text, University of Washington, Section VI.7, equations (VI-39)–(VI-44).
- Wikipedia, Effective population size, section on population size varying over time. <https://en.wikipedia.org/wiki/Effective_population_size>
