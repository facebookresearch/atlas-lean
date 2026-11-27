# Equilibria and Hopf bifurcations of an SIR model coupled to an incidence-driven vaccination game

**Model.** Let $S$, $I$ be susceptible and infectious fractions in an SIR population with birth/death rate $\mu$, transmission rate $\beta$ and recovery rate $\nu$, and let $p \in [0,1]$ be the fraction of newborns vaccinated. Vaccination opinions evolve by imitation at switching rate $k$, driven by perceived disease risk proportional to current incidence $\beta SI$, perceived vaccine risk proportional to uptake $p$, and a public-health push $\gamma \ge 0$:

$$\dot S = \mu(1-p) - \mu S - \beta SI, \qquad \dot I = \beta SI - (\nu + \mu)I, \qquad \dot p = k\Big(p(1-p)\big(\delta + \theta\beta SI - p\big) + \gamma(1-p)\Big),$$

with $\delta \ge 0$ the normalised net payoff of vaccinating and $\theta > 0$ the weight of incidence information. Let $\mathcal{R}_0 = \beta/(\nu + \mu)$ and $p_c = 1 - 1/\mathcal{R}_0$.

**Equilibria.**
- $E^P = (0, 0, 1)$ (all newborns vaccinated) is globally attractive if $\gamma > \bar\gamma = 1 - \delta$ and unstable if $\gamma < \bar\gamma$.
- For $\gamma < \bar\gamma$ there is a second disease-free equilibrium $E^0 = (1 - p^0, 0, p^0)$ with $p^0 = \frac{\delta + \sqrt{\delta^2 + 4\gamma}}{2} < 1$; with $\gamma_c = p_c(p_c - \delta) < \bar\gamma$, $E^0$ is globally attractive if $\gamma > \gamma_c$ (i.e. $p^0 > p_c$) and unstable if $\gamma < \gamma_c$.
- For $\gamma < \gamma_c$ a unique endemic equilibrium appears by transcritical bifurcation:

$$S^* = \frac{1}{\mathcal{R}_0}, \qquad I^* = \frac{\mu}{\nu + \mu}(p_c - p^*), \qquad p^* = \frac{\delta + \theta\mu p_c + \sqrt{(\delta + \theta\mu p_c)^2 + 4\gamma(1 + \theta\mu)}}{2(1 + \theta\mu)} .$$

**Theorem.** Put $q_1 = \mu + \beta I^*$, $q_2 = (\nu + \mu)\beta I^*$, $q_3 = \gamma/p^* + p^*$ and

$$W = q_1^2 q_3 + \theta\mu p^*\beta I^*(\beta I^* - \nu) + 2\sqrt{q_1 q_2 q_3\,(q_1 q_3 + \theta\mu p^*\beta I^*)} .$$

If $W \ge 0$, the endemic equilibrium $E^*$ is locally asymptotically stable for every switching rate $k$. If $W < 0$, there are $0 < k_1 < k_2$ such that $E^*$ is unstable for $k \in (k_1, k_2)$ and locally asymptotically stable for $k < k_1$ and $k > k_2$; Hopf bifurcations occur at $k = k_1$ and $k = k_2$, and for $k \in (k_1,k_2)$ orbits are oscillatory in the sense of Yakubovich.

So both slow and very fast opinion switching stabilise the endemic state, while intermediate rates can produce vaccine-scare oscillations. For large $k$ ($k = 1/\varepsilon$), geometric singular perturbation theory reduces the system to a two-dimensional slow flow on the critical manifold where $p$ follows the quasi-steady-state opinion.

## Proof sketch

The Jacobian at $E^*$ has a characteristic polynomial $\lambda^3 + a_2(k)\lambda^2 + a_1(k)\lambda + a_0(k)$ with coefficients affine in $k$ and all positive; by Routh–Hurwitz, stability is lost iff $a_2 a_1 - a_0 < 0$, which is a quadratic inequality in $k$. Its discriminant is governed by $W$: if $W \ge 0$ the quadratic is never negative, while if $W < 0$ it is negative exactly between its two positive roots $k_1 < k_2$, where a pair of eigenvalues crosses the imaginary axis transversally.

## Sources

- Rossella Della Marca, Alberto d’Onofrio, Mattia Sensi and Sara Sottile, "A geometric analysis of the impact of large but finite switching rates on vaccination evolutionary games", *Nonlinear Analysis: Real World Applications* 75 (2024), 103986, <https://doi.org/10.1016/j.nonrwa.2023.103986>. Preprint version: arXiv:2303.14248 (2023), section on the incidence-dependent evolutionary game (equilibria, global attractivity results proved in the Appendix, and Theorem 2) and the geometric singular perturbation section, <https://doi.org/10.48550/arXiv.2303.14248>.
