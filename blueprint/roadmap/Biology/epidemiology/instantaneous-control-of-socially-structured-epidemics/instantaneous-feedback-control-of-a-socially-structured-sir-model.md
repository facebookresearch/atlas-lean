# Instantaneous feedback control of a socially structured SIR model

**Model.** Individuals carry a social feature $a \in \Lambda$ (for example age). The densities $s(a,t)$, $i(a,t)$, $r(a,t)$, normalized so the population has total mass $1$, evolve by

$$\partial_t s = -s(a,t)\int_\Lambda \big(\beta(a, a_*) - u(a, a_*, t)\big)\, i(a_*, t)\, da_*, \qquad \partial_t i = -\partial_t s - \gamma(a) i, \qquad \partial_t r = \gamma(a) i,$$

with interaction kernel $\beta \ge 0$, recovery rate $\gamma(a) \ge 0$ and a contact-reduction control $0 \le u \le \min\{M, \beta\}$. Let $I(t) = \int_\Lambda i(a, t)\, da$ and let $\psi\colon [0, 1] \to \mathbb{R}_+$ be an increasing "perception" function of the infected total (for example $\psi(I) = I^q/q$).

**Proposition.**

1. *Short-horizon optimal control.* On a step $[t, t+h]$, minimize $J_h(u) = \psi(I(t+h)) + \frac12\int_{\Lambda^2}\nu |u|^2\, da\, da_*$ subject to the explicit Euler step of the model. The stationarity condition is

$$\nu(a, a_*, t)\, u(a, a_*, t) = h\, s(a, t)\, i(a_*, t)\, \psi'(I(t+h)).$$

2. *Feedback model.* Scaling the penalty as $\nu = h\kappa$ and letting $h \to 0$ gives the feedback-controlled model with effective kernel

$$\beta(a, a_*) - \frac{s(a, t)\, i(a_*, t)\, \psi'(I(t))}{\kappa(a, a_*, t)},$$

which reduces contacts most between groups whose susceptible and infected densities are both large, and more strongly as the perceived epidemic grows.
3. *Admissibility.* If $\beta(a, a_*) \ge \delta > 0$ and $\psi'$ is nondecreasing, the effective kernel stays nonnegative (so each $s(a, \cdot)$ is nonincreasing) provided

$$\delta\,\kappa(a, a_*, t) \ge s_0(a)\, \bar i(a_*)\, \psi'(\bar I) \quad \text{for all } (a, a_*),$$

where $\bar i(a_*)$ and $\bar I$ are the peak values of $i(a_*, \cdot)$ and $I$.
4. *Homogeneous mixing.* For $S' = -\big(\beta - S I \psi'(I)/\kappa\big) S I$, $I' = -S' - \gamma I$ with $\gamma, \kappa > 0$, the only equilibria have $I^* = 0$: the control flattens the epidemic curve but cannot hold a positive prevalence fixed.

## Expansion

Since $I(t+h) = I(t) + h\int_\Lambda \big[s(a,t)\int_\Lambda(\beta - u)\, i(a_*,t)\, da_* - \gamma(a) i(a,t)\big] da$, the derivative of $I(t+h)$ with respect to $u(a, a_*)$ is $-h\, s(a,t)\, i(a_*,t)$, and setting the first variation of $J_h$ to zero gives item 1; substituting $u = s\, i\, \psi'/\kappa$ into the dynamics gives item 2. This is suboptimal for the full horizon problem, whose optimality system couples the state to a backward adjoint system, but it needs only current information. Item 3 bounds $s(a,t) \le s_0(a)$, $i(a_*,t) \le \bar i(a_*)$ and $\psi'(I(t)) \le \psi'(\bar I)$; the bound is a consistency condition, since the peaks are those of the controlled solution. For item 4, a positive equilibrium needs both $\kappa\beta = S^* I^* \psi'(I^*)$ and $\big(\kappa\beta - S^* I^*\psi'(I^*)\big)S^* = \kappa\gamma I^*$, which together force $\gamma = 0$.

## Sources

- G. Albi, L. Pareschi, M. Zanella, "Control with uncertain data of socially structured compartmental epidemic models", *Journal of Mathematical Biology* 82 (2021) 63, sections "Optimal control of structured compartmental model" (Eqs. (2), (5)–(8)) and "Feedback controlled compartmental models" (Eqs. (9)–(15), Proposition 1). <https://doi.org/10.1007/s00285-021-01617-y> (PMC8141280).
