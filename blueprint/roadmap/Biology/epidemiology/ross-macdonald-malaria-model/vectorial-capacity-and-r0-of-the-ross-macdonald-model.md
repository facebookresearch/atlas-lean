# Vectorial capacity and the basic reproductive number of the Ross–Macdonald model

**Model.** With the notation of the [mosquito statics](mosquito-infection-statics-and-the-entomological-inoculation-rate.md) (mortality $g$, human feeding rate $a$, incubation period $n$, density $m = \varepsilon/g$, efficiencies $b$ and $c$), let humans recover at rate $r$ and let $X$ and $Z$ be the infectious fractions of humans and mosquitoes:

$$\dot Z = acX\,(e^{-gn} - Z) - gZ, \qquad \dot X = mabZ\,(1 - X) - rX \qquad \text{(Eqs. 18–19)}.$$

**Vectorial capacity.** The expected number of humans infected per infectious human per day when $b = c = 1$ is

$$C = \frac{m a^2 e^{-gn}}{g} = \varepsilon\, S^2\, P_e \qquad (S = a/g,\ P_e = e^{-gn};\ \text{Eq. 17}).$$

**Basic reproductive number.** 

$$R_0 = \frac{m a^2 b c\, e^{-gn}}{g\, r} = \frac{bcC}{r} = \frac{\varepsilon a^2 bc\, e^{-gn}}{g^2 r} \qquad \text{(Eqs. 22–23)},$$

the number of infected humans per infected human through one mosquito generation (the next-generation matrix of Eqs. 18–19 has spectral radius $\sqrt{R_0}$). Malaria invades iff $R_0 > 1$, i.e. iff the density exceeds Macdonald's critical density $m > g r e^{gn}/(a^2 bc)$.

**Equilibrium prevalence.** Using $\mathrm{EIR} \approx cCX$ (Eq. 21: $\dot X = bcCX(1-X) - rX$), the endemic equilibrium is $X^* = 1 - 1/R_0$ for $R_0 > 1$; using the exact EIR (Eq. 20), $X^* = b\,\mathrm{EIR}/(b\,\mathrm{EIR} + r)$, half the population being infected when $b\,\mathrm{EIR} = r$.

**Control sensitivity.** Relative to baseline, $R_0$ is divided by $\theta$ if emergence $\varepsilon$ is divided by $\theta$, by $\varphi$ if the infectious period $1/r$ is divided by $\varphi$, by $\psi^2$ if the feeding rate $a$ is divided by $\psi$, and by

$$\zeta^2\, e^{gn(\zeta - 1)}$$

if adult mortality is multiplied by $\zeta$ (density, survival through incubation and bites per infectious mosquito all fall). With $gn = 1$, doubling mortality divides $R_0$ by $4e \approx 11$ and tripling it by $9e^2 \approx 67$; the effects of combined measures multiply.

## Depends on

- [Mosquito infection statics and the entomological inoculation rate](mosquito-infection-statics-and-the-entomological-inoculation-rate.md)

## Expansion

At the disease-free state, one infectious human infects mosquitoes at rate $mac$ over $1/r$ days; each such mosquito survives incubation with probability $e^{-gn}$ and then delivers $a/g$ bites, each infecting a human with probability $b$. The product is $R_0$. Substituting $m = \varepsilon/g$ exposes the $g^{-2}e^{-gn}$ dependence, from which the mortality factor follows: replacing $g$ by $\zeta g$ multiplies $R_0$ by $\zeta^{-2}e^{-gn(\zeta-1)}$. Linearizing Eq. 21 at $X = 0$ gives growth rate $bcC - r$, so $bcC > r$ is the same threshold. The approximation of Eq. 21 overestimates equilibrium prevalence because $cCX$ exceeds the exact EIR by the factor $1 + acX/g$.

## Sources

- D. L. Smith and F. E. McKenzie, "Statics and dynamics of malaria infection in *Anopheles* mosquitoes", Malaria Journal 3 (2004) 13, Eqs. 17–23 and sections "Threshold Criteria", "Proportion of Infected Humans", "Malaria Control", <https://doi.org/10.1186/1475-2875-3-13> (PMC449722).
- G. Macdonald, *The Epidemiology and Control of Malaria*, Oxford University Press, London, 1957.
