# Transient quanta concentration and dose in a well-mixed room

**Setting.** A room of volume $V > 0$ contains $I \ge 0$ infectious occupants, each emitting airborne infectious quanta at a constant rate $\mathrm{ER}_q \ge 0$ (quanta per hour). A *quantum* is the dose of airborne droplet nuclei that infects a susceptible with probability $1 - e^{-1} \approx 63\%$. Infectious quanta are removed by first-order processes at the total rate

$$\mathrm{IVRR} = \mathrm{AER} + k + \lambda > 0,$$

the sum of the air exchange rate $\mathrm{AER}$, the deposition rate $k$ and the viral inactivation rate $\lambda$. Assume the room is instantaneously and evenly mixed, the removal rate is constant, and the latent period is longer than the exposure, so that no new emitters appear. The quanta concentration $n(t)$ then solves the mass balance

$$\frac{dn}{dt} = \frac{\mathrm{ER}_q\, I}{V} - \mathrm{IVRR}\; n, \qquad n(0) = n_0 \ge 0 .$$

**Proposition.**

1. (Concentration) For $t \ge 0$,

$$n(t) = n_0\, e^{-\mathrm{IVRR}\, t} + \frac{\mathrm{ER}_q\, I}{\mathrm{IVRR}\; V}\left(1 - e^{-\mathrm{IVRR}\, t}\right),$$

which increases (or decreases) monotonically to the steady state $n_\infty = \mathrm{ER}_q I / (\mathrm{IVRR}\, V)$.
2. (Dose) A susceptible inhaling at constant rate $\mathrm{IR}$ for a time $T$ receives the dose

$$D_q = \mathrm{IR}\int_0^T n(t)\, dt = \mathrm{IR}\left[\, n_\infty T + (n_0 - n_\infty)\,\frac{1 - e^{-\mathrm{IVRR}\, T}}{\mathrm{IVRR}} \right].$$

3. (Exponential dose-response) If quanta are Poisson-distributed in the inhaled air, the probability of infection is

$$P_I = 1 - e^{-D_q}.$$

## Expansion

The mass balance is linear with constant coefficients, so (1) is the variation-of-constants solution. Integrating (1) term by term gives (2): $\int_0^T e^{-\mathrm{IVRR}\,t}dt = (1 - e^{-\mathrm{IVRR}\,T})/\mathrm{IVRR}$. For (3), if the number of quanta inhaled is Poisson with mean $D_q$ and each quantum independently suffices to infect, infection fails only when zero quanta are inhaled, which has probability $e^{-D_q}$; one quantum on average gives $1 - e^{-1}$, which is the definition of a quantum. When $n_0 = n_\infty$ or $T \gg 1/\mathrm{IVRR}$ the transient term vanishes and (2)–(3) reduce to the steady-state Wells–Riley formula $P_I = 1 - \exp(-\mathrm{IR}\,\mathrm{ER}_q\, I\, T/Q)$ with $Q = \mathrm{IVRR}\cdot V$; for short exposures in a room that starts clean, the transient term makes the dose, and so the risk, smaller than the steady-state formula predicts. The model ignores size-dependent settling (a single $k$ is used), spatial gradients near the emitter, and host heterogeneity in susceptibility, which would replace the exponential law by a beta-Poisson law.

## Sources

- G. Buonanno, L. Morawska, L. Stabile, "Quantitative assessment of the risk of airborne transmission of SARS-CoV-2 infection: Prospective and retrospective applications", Environment International 145 (2020) 106112, Section 2.1, Eqs. (2)–(4), <https://doi.org/10.1016/j.envint.2020.106112> (PMC7474922).
- L. Gammaitoni, M. C. Nucci, "Using a mathematical model to evaluate the efficacy of TB control measures", Emerging Infectious Diseases 3 (1997) 335–342, <https://doi.org/10.3201/eid0303.970310>.
- E. C. Riley, G. Murphy, R. L. Riley, "Airborne spread of measles in a suburban elementary school", American Journal of Epidemiology 107 (1978) 421–432, <https://doi.org/10.1093/oxfordjournals.aje.a112560>.
