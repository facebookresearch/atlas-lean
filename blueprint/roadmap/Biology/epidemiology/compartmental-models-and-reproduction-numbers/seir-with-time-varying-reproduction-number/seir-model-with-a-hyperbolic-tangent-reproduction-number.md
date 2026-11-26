# SEIR model with a hyperbolic-tangent reproduction number

**Model.** For a population of size $N$ with latency rate $\alpha$ and recovery rate $\gamma$ (latent period $A = 1/\alpha$, infectious period $C = 1/\gamma$), the SEIR model with a time-varying effective reproduction number $R(t)$ is

$$\dot S = -R(t)\,\gamma\,\frac{S I}{N}, \quad \dot E = R(t)\,\gamma\,\frac{S I}{N} - \alpha E, \quad \dot I = \alpha E - \gamma I, \quad \dot{\mathcal R} = \gamma I,$$

i.e. the SEIR system with contact rate $\beta(t) = R(t)\,\gamma$; the recovered compartment is written $\mathcal R$ to keep it apart from the reproduction number. Interventions are encoded by the hyperbolic-tangent ansatz

$$R(t) = R_0 - \tfrac12\Big[1 + \tanh\!\Big(\frac{t - t^*}{T}\Big)\Big]\,(R_0 - R_t),$$

with four parameters: the basic reproduction number $R_0$ before interventions, the reproduction number $R_t$ under the interventions, the adaptation time $t^*$ (midpoint of the transition) and the transition time $T > 0$ (its duration scale).

**Properties.**

- $R(t) \to R_0$ as $t \to -\infty$, $R(t) \to R_t$ as $t \to +\infty$, $R(t^*) = (R_0 + R_t)/2$, and $R$ is monotone between the two values; $R'(t^*) = -(R_0 - R_t)/(2T)$.
- $S + E + I + \mathcal R$ is conserved for any measurable $R(\cdot) \ge 0$, and integrating $\dot S / S = -R(t)\,\dot{\mathcal R}/N$ gives

$$S(t) = S(0)\exp\!\Big(-\frac{1}{N}\int_0^t R(u)\,\dot{\mathcal R}(u)\,du\Big),$$

so the final susceptible fraction under $R(\cdot)$ is at least as large as under the constant value $R_0$ whenever $R(t) \le R_0$ for all $t$: the infections that the intervention prevents are never "made up" in the final-size relation.
- **Constrained equilibrium (approximation).** Treating the reproduction number as constant and equal to $R_t$ from the time $t^* + T/2$ onward, and applying the [Lambert-W final-size formula](lambert-w-solution-of-the-seir-final-size-relation.md) with the fractions $s_t, r_t$ at that time, gives the temporarily stable state

$$s^*_\infty = -\frac{1}{R_t}\,W_0\!\big(-s_t R_t\, e^{-R_t (1 - r_t)}\big), \qquad r^*_\infty = 1 - s^*_\infty,$$

with $s_\infty \le s^*_\infty$ and $r^*_\infty \le r_\infty$ relative to the unconstrained final size when $R_t \le R_0$. This state is stable only while the interventions hold; it is not the herd-immunity equilibrium, and lifting the interventions (returning $R$ toward $R_0$ with $R_0 s^*_\infty > 1$) restarts growth.

## Depends on

- [Lambert-W solution of the SEIR final-size relation](lambert-w-solution-of-the-seir-final-size-relation.md)
- [SEIR epidemic model](../../seir-epidemic-model/README.md)

## Expansion

The limits and the midpoint value follow from $\tanh(\pm\infty) = \pm 1$ and $\tanh 0 = 0$. The integrated identity holds because $\dot S / S = -R(t)\gamma I / N = -R(t)\dot{\mathcal R} / N$; with $R(t) \le R_0$ and $\dot{\mathcal R} \ge 0$, writing $s_0, e_0, i_0, r_0$ for the initial fractions, the limit $\tilde s = \lim S/N$ under $R(\cdot)$ satisfies $\varphi(\tilde s) \ge 0$ for $\varphi(s) = s - s_0 e^{-R_0(1 - s - r_0)}$. The function $\varphi$ is strictly concave, vanishes at the constant-$R_0$ final size $s_\infty$ and at a second root $\bar s$, and $\varphi(s_0) = s_0\big(1 - e^{-R_0(e_0 + i_0)}\big) \ge 0$, so $\{\varphi \ge 0\} = [s_\infty, \bar s] \ni s_0 \ge \tilde s$; hence $\tilde s \ge s_\infty$. The constrained equilibrium is exact if $R(t)$ were literally equal to $R_t$ after $t^* + T/2$; for the smooth ansatz, $R(t^* + T/2) = R_0 - \tfrac12(1 + \tanh \tfrac12)(R_0 - R_t)$ is only about $73\%$ of the way to $R_t$, so it is an approximation. In the source, $R_0$, $R_t$, $t^*$ and $T$ were inferred per country by Bayesian fitting to reported cases, and the inflection time $t^*$ was compared with mobility reductions (mean delay about 17 days).

## Sources

- K. Linka, M. Peirlinck, E. Kuhl, "The reproduction number of COVID-19 and its correlation with public health interventions", Computational Mechanics (2020), Methods ("Epidemiology modeling") and Appendix, Eqs. (18)–(22), <https://doi.org/10.1007/s00466-020-01880-8> (PMC7385940).
