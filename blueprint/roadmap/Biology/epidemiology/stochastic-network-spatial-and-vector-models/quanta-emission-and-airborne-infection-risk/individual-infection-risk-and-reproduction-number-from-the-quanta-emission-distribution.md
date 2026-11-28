# Individual infection risk and reproduction number from the quanta emission distribution

**Setting.** In the [well-mixed room model](transient-quanta-concentration-and-dose-in-a-well-mixed-room.md) with one infectious occupant ($I = 1$) and $n_0 = 0$, fix the room, the removal rate, the exposure time $T$ and the inhalation rate $\mathrm{IR}$ of the exposed. The quanta emission rate of the infected occupant is computed forward from the sputum viral load,

$$\mathrm{ER}_q = c_v\, c_i\, \mathrm{IR}_e\, V_d, \qquad c_i = \frac{1}{c_{\mathrm{RNA}}\, c_{\mathrm{PFU}}},$$

where $c_v$ is the viral load (RNA copies per mL), $c_{\mathrm{RNA}}$ the RNA copies per plaque-forming unit, $c_{\mathrm{PFU}}$ the plaque-forming units per quantum, $\mathrm{IR}_e$ the emitter's exhalation rate and $V_d$ the expired droplet volume concentration (mL per m$^3$), which depends on the expiratory activity. Treat $\mathrm{ER}_q$ as a random variable with law $\mu$ on $[0,\infty)$ (log-normal in the source), induced by the variability of $c_v$, $V_d$, $c_{\mathrm{RNA}}$ and $c_{\mathrm{PFU}}$. Write $P_I(e)$ for the infection probability when $\mathrm{ER}_q = e$; by the dose-response law $P_I(e) = 1 - e^{-\kappa e}$ with

$$\kappa = \frac{\mathrm{IR}}{\mathrm{IVRR}\; V}\left[\, T - \frac{1 - e^{-\mathrm{IVRR}\, T}}{\mathrm{IVRR}} \right] \ge 0 .$$

The *individual infection risk* is

$$R = \int_0^\infty P_I(e)\, \mu(de),$$

and, for $S$ exposed susceptibles, the event reproduction number is $R_0^{\mathrm{event}} = R \cdot S$.

**Proposition.**

1. $R = 1 - \mathcal{L}_\mu(\kappa)$, where $\mathcal{L}_\mu(s) = \int e^{-s e}\,\mu(de)$ is the Laplace transform of the emission law. In particular $R$ is increasing and concave in the exposure parameter $\kappa$, and $R \to \mu(\{e > 0\})$ as $T \to \infty$.
2. (Jensen bound) $R \le P_I(\mathbb{E}\,\mathrm{ER}_q) = 1 - \exp(-\kappa\, \mathbb{E}\,\mathrm{ER}_q)$ whenever $\mathbb{E}\,\mathrm{ER}_q < \infty$: plugging in the mean emission rate overstates the risk.
3. (Acceptable exposure time) For a target risk $R^\ast \in (0, \mu(\{e>0\}))$ there is a unique maximum exposure time $T^\ast$ with $R(T^\ast) = R^\ast$, and $R \le R^\ast$ exactly for $T \le T^\ast$.
4. (Crowding) $R_0^{\mathrm{event}} < 1$ if and only if $S < 1/R$.

## Depends on

- [Transient quanta concentration and dose in a well-mixed room](transient-quanta-concentration-and-dose-in-a-well-mixed-room.md)

## Proof depends on

- [Jensen's inequality](../../../../MeasureTheory/integration/jensen-s-inequality-for-integrals/jensen-s-inequality/jensen-inequality.md)

## Expansion

With $n_0 = 0$ the dose is linear in the emission rate, $D_q = \kappa\, \mathrm{ER}_q$, by part 2 of the room-model proposition, so $P_I(e) = 1 - e^{-\kappa e}$ and (1) is the definition of $R$ rewritten. The bracket defining $\kappa$ is $\int_0^T (1 - e^{-\mathrm{IVRR}\,t})\,dt$, which is strictly increasing in $T$, and $R$ is strictly increasing and continuous in $\kappa$ (dominated convergence) whenever $\mu(\{e>0\}) > 0$; this gives (3). (2) is Jensen's inequality for the concave map $e \mapsto 1 - e^{-\kappa e}$. (4) is immediate. With $\log_{10}\mathrm{ER}_q$ normal (standard deviation $0.72$ for every expiratory activity in the source), emission spans several orders of magnitude, so a few high emitters dominate $R$: the authors attribute large indoor outbreaks to "superspreading events", where an unremarkable emitter meets high crowding, low ventilation and long exposure, rather than to rare superspreading individuals.

## Sources

- G. Buonanno, L. Morawska, L. Stabile, "Quantitative assessment of the risk of airborne transmission of SARS-CoV-2 infection: Prospective and retrospective applications", Environment International 145 (2020) 106112, Section 2.1.1, Eq. (1), Section 2.2, Eqs. (5)–(6), and Table 2, <https://doi.org/10.1016/j.envint.2020.106112> (PMC7474922).
