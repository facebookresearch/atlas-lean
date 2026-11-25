# Segregational load at an overdominant equilibrium

Let genotypes $AA$, $Aa$, $aa$ have viabilities $1 - s$, $1$, $1 - t$ with $0 < s, t \le 1$, so that under
random mating the frequency of $A$ has the interior equilibrium $p_e = t/(s + t)$
([overdominance](one-locus-viability-selection-regimes.md)). At this equilibrium the mean viability is

$$\bar w = 1 - s p_e^2 - t (1 - p_e)^2 = 1 - \frac{st}{s + t},$$

so the segregational load, the reduction relative to the fittest genotype $Aa$, is $st/(s + t)$, half
the harmonic mean of $s$ and $t$; it is at most $1/2$. If the population at allele frequency $p_e$ has
the [genotype frequencies of inbreeding coefficient $F$](../../inbreeding-and-regular-systems-of-mating/genotype-frequencies-under-inbreeding.md),
its mean viability is

$$\bar w(F) = 1 - (1 + F) \frac{st}{s + t},$$

so the load becomes $(1 + F)\,st/(s + t)$ and complete inbreeding doubles it.

## Depends on

- [Directional selection, overdominance and underdominance at one locus](one-locus-viability-selection-regimes.md)
- [Genotype frequencies of an inbred individual](../../inbreeding-and-regular-systems-of-mating/genotype-frequencies-under-inbreeding.md)

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section II.8 "Selection and Fitness", subsection "Segregational load", equation (II-119), p. 99; Chapter II, Exercise 14,
  p. 135 (the bound $1/2$); Section V.14, equation (V-48), p. 244 (mean fitness under inbreeding).
