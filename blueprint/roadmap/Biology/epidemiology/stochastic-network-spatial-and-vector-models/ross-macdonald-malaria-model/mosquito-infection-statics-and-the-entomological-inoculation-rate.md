# Mosquito infection statics and the entomological inoculation rate

**Classic assumptions.** Adult mosquitoes die at constant per-capita rate $g > 0$ (no senescence), emerge at constant rate $\varepsilon$ per human so that the density per human is $m = \varepsilon/g$, feed every $1/f$ days with a fraction $Q$ of bites on humans, and bite humans at random at rate $a = Qf$. A constant fraction $X \in [0,1]$ of humans is infectious; a bite on an infectious human infects a mosquito with probability $c$, and an infected mosquito becomes infectious after an extrinsic incubation period $n$ and never clears infection.

**Formulas.**

- Survivorship to age $A$: $\lambda(A) = e^{-gA}$ (Eq. 1); daily survival $p = e^{-g}$, mean lifespan $1/g$.
- Stability index (human bites per lifetime): $S = a/g$.
- Human blood index, the fraction of mosquitoes that have ever fed on a human: $\mathrm{HBI} = \dfrac{a}{a+g}$ (Eq. 5), from $\eta(A) = 1 - e^{-aA}$ (Eq. 4).
- Proportion of mosquitoes ever infected: $Y = \dfrac{acX}{g + acX}$ (Eq. 7), from $\nu(A) = 1 - e^{-acXA}$ (Eq. 6).
- Sporozoite rate (proportion infectious): $Z = Y\,P_e = \dfrac{acX}{g + acX}\,e^{-gn}$ (Eq. 8), with $P_e = e^{-gn}$ the probability of surviving the incubation period.
- Entomological inoculation rate (infectious bites per human per day):

$$\mathrm{EIR} = maZ = \frac{m a^2 c X e^{-gn}}{g + acX}.$$

**Small-prevalence limit.** With vectorial capacity $C = m a^2 e^{-gn}/g$,

$$\mathrm{EIR} = cCX\,\frac{g}{g + acX} \le cCX, \qquad \frac{d\,\mathrm{EIR}}{dX}\Big|_{X=0} = cC,$$

so $cCX$ approximates EIR when $X$ is small and overestimates it by the factor $1 + acX/g$.

**Dynamic form.** The sporozoite rate obeys $\dot Z = acX\,(e^{-gn} - Z) - gZ$ (Eq. 18), whose equilibrium is Eq. 8.

## Expansion

Each static proportion is a ratio of waiting times computed from a cohort: a mosquito alive at age $A$ has escaped death (probability $e^{-gA}$) and has experienced a competing exponential event (human bite at rate $a$, or infection at rate $acX$). Integrating $\eta(A)\lambda(A)$ against the age density gives $\int_0^\infty g e^{-gA}(1 - e^{-aA})\,dA = a/(a+g)$, and the same computation with rate $acX$ gives $Y$. Infectiousness further requires survival of $n$ days, contributing the factor $e^{-gn}$ by memorylessness. EIR is the human biting rate $ma$ times the sporozoite rate. The formulas reduce to Macdonald's when $c = 1$ and, read backwards, let $g$, $a$, $cX$ and $n$ be estimated successively from mosquito survival, the HBI, the infected proportion and the sporozoite rate.

## Sources

- D. L. Smith and F. E. McKenzie, "Statics and dynamics of malaria infection in *Anopheles* mosquitoes", Malaria Journal 3 (2004) 13, Eqs. 1–8, 17–18 and section "EIR & Vectorial Capacity", <https://doi.org/10.1186/1475-2875-3-13> (PMC449722).
