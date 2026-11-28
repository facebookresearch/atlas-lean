# Critical manifold and singular orbits of the Karma model

The space-clamped **Karma model** for a membrane potential $E$ and a slow gating variable $n$ is

$$E' = -E + 2\left(E^* - n^M\right)\left(E^2 - \delta E^3\right) + I, \qquad n' = \varepsilon\left(\frac{1}{n_B}\,\theta(E - 1) - n\right),$$

with $E^* = 1.5$, $\delta = 0.25$, $M \gg 1$, $0 < n_B < 1$, the rectifier $\theta(x) = \max\{0, x\}$ (which the source uses in place of Karma's Heaviside step function), applied current $I$ and $0 < \varepsilon \ll 1$ (Gonzalez Herrero, Kuehn and Tsaneva-Atanasova 2021, system (3.1)).

**Theorem ($I = 0$).** In the singular limit $\varepsilon = 0$ the critical manifold is

$$C_0 = \left\{(E,n) : E = 0\ \text{ or }\ n^M = E^* - \frac{1}{2E(1-\delta E)}\right\},$$

normally hyperbolic except at the generic fold point $p_F = (2, 1)$, with attracting outer branches and a repelling middle branch. There are three equilibria: a stable one at the origin (rest), a saddle where the repelling branch meets the $E$-axis, and an unstable equilibrium on the repelling branch. Every candidate orbit is a concatenation of fast jumps to the outer branches and slow drift along them; it converges to the rest state unless it is one of the two unstable equilibria or the unique heteroclinic orbit between them (Theorem 3). Away from the heteroclinic segment, candidate orbits persist as true orbits for small $\varepsilon > 0$ (Theorem 4), and the heteroclinic segment persists as a heteroclinic orbit (Theorem 5).

**Theorem ($I > 0$; Theorem 6).** In the singular limit the critical manifold becomes $n^M = E^* - \frac{E - I}{2E^2(1-\delta E)}$, and every candidate orbit is a concatenation of fast segments converging to the attracting outer branches and slow segments on the critical manifold. Let $I_2$ be the value of $I$ at which the equilibrium with $n > 0$ changes from unstable to stable as $I$ increases. Then:

- for $I < I_0 \approx 0.08718$ there are three equilibria, with a stable node and a saddle on the $E$-axis; if $I < I_2$ the behaviour is equivalent to the case $I = 0$, and otherwise the system is bistable;
- for $I_0 < I < I_1 = 4/9$ there is a unique equilibrium; if $I < I_2$ it is unstable and the system has a stable relaxation oscillation, and otherwise the equilibrium is globally stable although there are relaxation pulses;
- for $I > I_1$ ($> I_2$) the middle branch disappears, the critical manifold is attracting everywhere and the unique equilibrium is globally stable.

**Persistence (Theorem 7).** Let $E_-(I) = \bigl((4 + 3I) - \sqrt{(4+3I)^2 - 64I}\bigr)/4$ be the lower curve of non-hyperbolic equilibria of the layer problem (source Eq. (3.13), for $\delta = 0.25$). Whenever $E_-(I) \ne 1$, candidate orbits of the singular limit with $I > 0$, away from the bifurcation points $I_0$ and $I_2$, can be perturbed to solution curves of the full system with $\varepsilon > 0$.

Unlike FitzHugh–Nagumo, whose cubic critical manifold has a single equilibrium at rest, the Karma model has a saddle and an unstable node on the repelling branch and a non-smooth slow flow at $E = 1$, which produces the heteroclinic connection and the different excitability thresholds.

## Expansion

Equilibria of the layer problem satisfy $E = 0$ or $1 = 2(E^* - n^M)E(1-\delta E)$, giving the formula for $C_0$. The layer Jacobian $J = -1 + 2(E^* - n^M)(2E - 3\delta E^2)$ is negative on the outer branches, positive on the middle branch and vanishes only at $p_F$. The reduced flow $\dot n = \theta(E-1)/n_B - n$ on $C_0$ is piecewise linear and meets $C_0$ three times. Fenichel theory is applied separately on $E < 1$ and $E > 1$ to handle the kink of $\theta$ at $0$, and continuity extends orbits across $E = 1$.

## Sources

- M. E. Gonzalez Herrero, C. Kuehn and K. Tsaneva-Atanasova, *Reduced models of cardiomyocytes excitability: comparing Karma and FitzHugh–Nagumo*, Bulletin of Mathematical Biology 83 (2021), the choice $\theta(x) = \max\{0, x\}$ before Eq. (2.13), system (3.1), Remark 1, Eqs. (3.4)–(3.11) and Theorems 3–7. <https://doi.org/10.1007/s11538-021-00898-0> (PMCID: PMC8253715)
