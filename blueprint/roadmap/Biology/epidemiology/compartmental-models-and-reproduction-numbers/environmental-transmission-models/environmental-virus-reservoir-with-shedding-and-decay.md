# Environmental virus reservoir with shedding and decay

**Model.** Infected hosts $I(t)$ shed virus into an environmental pool $V(t)$ at per-capita rate $\omega$, and environmental virus is cleared (decays) at rate $c > 0$, which may depend on temperature and season:

$$\frac{dV}{dt} = \omega I(t) - c\,V(t).$$

Susceptible hosts are infected from the environment at rate $\rho\,(1 - e^{-\alpha V(t)})$ per host, with exposure rate $\rho$ and per-virion infectiousness $\alpha$, as for an [exponential dose–response](exponential-dose-response-from-independent-exposures.md), in addition to direct transmission.

**Proposition.**

1. *Rescaling.* With $\tilde V = V/\omega$ (virus measured in units of the per-capita shedding rate), $d\tilde V/dt = I - c\tilde V$ and the environmental infection rate is $\rho\,(1 - e^{-(\alpha\omega)\tilde V})$; the dynamics depend on $\alpha$ and $\omega$ only through the product $\alpha\omega$ (rescaled per-virion infectiousness), and on $\rho$ separately.
2. *Piecewise-constant shedding.* If $I(t) = I$ is constant on an interval $[t_0, t_0 + \Delta]$, then for $0 \le s \le \Delta$

$$V(t_0 + s) = V(t_0)\, e^{-cs} + \frac{\omega I}{c}\big(1 - e^{-cs}\big),$$

so $V$ relaxes exponentially, at rate $c$, toward the quasi-equilibrium $\omega I / c$; with no hosts present ($I = 0$) the pool decays as $V(t_0)e^{-cs}$.
3. *Persistence across seasons.* For a site vacated for a period $\Delta$ (for example a breeding ground in winter), the virus surviving to the hosts' return is the fraction $e^{-c\Delta}$ of the pool left at departure; slow decay (cold water, small $c$) lets the environment carry infection between seasons even after infection has died out in the host population.
4. *Reproduction number.* Near a disease-free state with $S_0$ susceptibles, direct transmission rate $\beta$ per susceptible–infective pair, and infectious period with removal rate $\gamma + d$ (recovery plus death), one infective generates on average

$$R_0 = \frac{\beta S_0}{\gamma + d} + \frac{\alpha\rho\omega\, S_0}{c\,(\gamma + d)}$$

secondary infections, the second term through the environment.

## Depends on

- [Exponential dose–response from independent exposures](exponential-dose-response-from-independent-exposures.md)

## Expansion

Property 1 is immediate by substitution. Property 2 is the solution of a linear first-order equation with constant forcing. Property 4 follows from the next-generation method with infected compartments $(I, V)$: an infective lives $1/(\gamma + d)$ time units, infects $\beta S_0$ hosts per unit time directly, and sheds $\omega$ virions per unit time, each of which persists $1/c$ time units on average; linearizing the environmental rate at $V = 0$, $\rho(1 - e^{-\alpha V}) = \alpha\rho V + O(V^2)$, so each virion infects at rate $\alpha\rho S_0$ near the disease-free state; summing the two pathways gives the formula. The environmental term is what allows recurrent epidemics in wild waterfowl when host turnover alone is too slow to sustain transmission, because virus deposited during one season seeds the next.

## Sources

- Breban R, Drake JM, Stallknecht DE, Rohani P, "The role of environmental transmission in recurrent avian influenza epidemics" (2009), sections "Model" and "Hybrid model" (Equation (1) for virus kinetics, rescaling by the shedding rate, and the within-season solutions (12)–(15)); the reproduction number in item 4 is derived here, <https://doi.org/10.1371/journal.pcbi.1000346>, PMCID PMC2660440.
