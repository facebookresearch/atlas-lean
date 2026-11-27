# Quasi-neutral coexistence curve and its breakdown in the helper virus–DVG–satellite RNA model

**Model.** Let $V, S, D \ge 0$ be the densities of a helper virus, its satellite RNA and its defective viral genomes (DVGs) inside a cell, $p \in [0,1]$ the fraction of available viral RNA-dependent RNA polymerase, and $\Omega = 1 - V - S - D$ the free resources. With replication rates $\alpha, \beta, \gamma > 0$, DVG production fraction $\omega \in (0,1)$, RNA degradation $\varepsilon$, polymerase synthesis $\kappa$ and decay $\varepsilon_p$:

$$\dot V = \alpha(1-\omega)Vp\Omega - \varepsilon V,\quad \dot S = \beta S p\Omega - \varepsilon S,\quad \dot D = (\omega\alpha V + \gamma D)p\Omega - \varepsilon D,\quad \dot p = \kappa V(1-p) - \varepsilon_p p .$$

**Results.**
1. There are no periodic orbits in the biologically relevant region.
2. *Satellite-free equilibria* $Q_1 = (V_1, 0, D_1, p_1)$ require $\alpha(1-\omega) > \max\{\gamma,\varepsilon\}$; at such an equilibrium $p_1\Omega(x_1) = \varepsilon/(\alpha(1-\omega))$.
3. *Coexistence equilibria* ($S \neq 0$) exist only if

$$\alpha(1-\omega) = \beta \quad\text{and}\quad \beta > \gamma ;$$

then they form a curve $\Gamma$ (a piece of a hyperbola in the $(V,S)$ coordinates) inside the plane $D = \frac{\beta\omega}{(\beta-\gamma)(1-\omega)}V$, with $p = 1 - \varepsilon_p/(\kappa V + \varepsilon_p)$. In this case the plane is invariant and $S/V$ is a first integral, so $\Gamma$ is a quasi-neutral curve of non-isolated equilibria.
4. Let $\mu = \alpha - \alpha^*$ with $\alpha^* = \beta/(1-\omega)$. For $\mu < 0$, every interior orbit tends to the origin (extinction of all three RNAs) when no other attractor is present, and orbits passing near the former location of $\Gamma$ spend a time bounded below by $\frac{\tilde K\alpha}{\varepsilon}\,|\mu|^{-1}$ there: transients obey the scaling law $\tau \sim |\mu|^{-1}$.

## Expansion

Because $\dot S/S - \dot V/V = (\beta - \alpha(1-\omega))\,p\Omega$, the ratio $S/V$ grows, decays or is conserved according to the sign of $\beta - \alpha(1-\omega)$; coexistence of satellite and helper requires exact equality of their effective replication rates, which is why it occurs only on a codimension-one parameter set and as a continuum of equilibria. Perturbing $\alpha$ away from $\alpha^*$ destroys $\Gamma$ (a global, non-local bifurcation), but the slow drift of $S/V$ at rate proportional to $|\mu|$ near the ghost of $\Gamma$ produces long bottleneck transients whose duration scales like $|\mu|^{-1}$.

## Sources

- Oriol Llopis-Almela, J. Tomas Lazaro, Santiago F. Elena and Josep Sardanyes, "Global bifurcation in a virus, defective genomes, satellite RNAs tripartite system: Breakdown of a coexistence quasi-neutral curve", Chaos, Solitons & Fractals 192 (2025), 116037, <https://doi.org/10.1016/j.chaos.2025.116037>; numbering as in arXiv:2411.00070: system (1)–(4) and Propositions 1–7.
