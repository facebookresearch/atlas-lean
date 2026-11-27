# Incomplete canard explosion between type I and type II excitability

**Setting.** A planar slow–fast neuron model with cubic critical manifold, written near its lower fold $F^-$ in the normal form

$$x' = \varepsilon\big(c\,y - \sigma x - a + O(x^2,y^3,xy,\varepsilon y^2)\big), \qquad y' = y^2 - x + \beta y^3 + O(y^4),$$

where $a$ is the current-like bifurcation parameter and $c$ the slope of the slow nullcline at the fold. For $\varepsilon = 0$ there is a cusp of equilibria at $c_{\mathrm{cusp}}$, and a saddle-node branch meets the $c$-axis at $c_{\mathrm{sn}}^- \in (0, c_{\mathrm{cusp}})$. The equilibrium equation near the fold is $-a + c y - y^2 + O(y^3) = 0$, so a saddle-node of equilibria occurs at

$$a_{\mathrm{sn}}^+ = \frac{c^2}{4} + O(c^3).$$

**Theorem.** Fix $0 < c < c_{\mathrm{sn}}^- < c_{\mathrm{cusp}}$ and $0 < \varepsilon \ll 1$. There is an unstable equilibrium on the middle branch bounded away from $F^-$, and there are parameter values

$$0 < a_{\mathrm{snpo}}(\varepsilon) < a_\ell(\varepsilon) < a_s(\varepsilon) < a_c(\varepsilon) < a_h(\varepsilon) < a_{\mathrm{sn}}^+(\varepsilon),$$

all tending to $0$ as $\varepsilon \to 0$ except $a_{\mathrm{sn}}^+$, such that as $a$ decreases:
1. for $a > a_{\mathrm{sn}}^+$ a large stable relaxation cycle exists; at $a_{\mathrm{sn}}^+$ a saddle-node of equilibria creates a saddle $p_+$ and an unstable focus or node $p_-$ on the middle branch inside it;
2. at $a_h$, $p_-$ changes stability in a subcritical singular Andronov–Hopf bifurcation, and for $a_c < a < a_h$ repelling small cycles surround the stable focus;
3. for $a_s < a < a_c$ small jump-back canard cycles grow rapidly (canard explosion) while the relaxation cycle becomes a large jump-forward canard cycle;
4. at $a_s$ the explosion terminates in a small jump-back homoclinic loop of canard type at the saddle $p_+$; for $a_\ell < a < a_s$ only the large stable canard cycle remains;
5. at $a_\ell$ a large-amplitude homoclinic loop of canard type appears, and below it large canard cycles grow until they vanish in a saddle-node of limit cycles at $a_{\mathrm{snpo}}$.
The gap $a_h - a_c$ is $O(\varepsilon)$, while $a_c$, $a_s$, $a_\ell$ and $a_{\mathrm{snpo}}$ are exponentially close to each other.

## Depends on

- [Fold normal form and the singular Andronov–Hopf canard values](fold-normal-form-and-the-singular-andronov-hopf-canard-values.md)

## Expansion

Below the cusp, the extra saddle $p_+$ on the repelling branch interrupts the canard family: canard cycles that would normally grow continuously into relaxation oscillations (a complete explosion, type II) instead collide with $p_+$ in a homoclinic bifurcation before reaching full size. This is the first step of the transition toward type I excitability, whose organizing centre at $a = c = 0$ is a singular Bogdanov–Takens point with a saddle-node homoclinic (SNIC) orbit. The ordering of the parameter values follows from tracking slow-manifold separatrices through the fold with exponentially small splitting, together with a Melnikov-type regular breaking of the homoclinic connections.

## Sources

- P. De Maesschalck, M. Wechselberger, "Neural excitability and singular bifurcations", Journal of Mathematical Neuroscience 5:16 (2015), Section 5, Theorem 2 and Eq (25), with Fig 6, <https://doi.org/10.1186/s13408-015-0029-2>, PMCID PMC4526515.
