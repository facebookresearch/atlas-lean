# Predator–prey model with fear, prey refuge and additional food

**Model.** Prey $u$ and predator $v$ biomasses satisfy

$$\frac{du}{dt} = \frac{ru}{1 + \omega v} - du - pu^2 - \frac{a(1-m)uv}{s + (1-m)u + lv}, \qquad \frac{dv}{dt} = \frac{ca\{(1-m)u + \eta A\}v}{s + (1-m)u + lv} - \mu_1 v - \mu_2 v^2,$$

with $s = b + \alpha\eta A$ and positive parameters, $r > d$. Here fear of predators reduces prey birth by the factor $1/(1 + \omega v)$, a fraction $m$ of prey hides in a refuge, predators also eat an additional food of biomass $A$ (quality $\alpha$, encounter rate $\eta$) through a Beddington–DeAngelis response with predator interference $l$, and predators compete intraspecifically at rate $\mu_2$. In space, $u$ and $v$ diffuse with coefficients $d_1, d_2$; in the *nonlocal* version the fear term becomes $ru/(1 + \omega(\phi_\delta * v))$, with $\phi_\delta$ a nonnegative compactly supported kernel of range $\delta$, so prey respond to predators within distance $\delta$.

**Theorem.**

1. *(Well-posedness.)* Solutions starting in $\mathbb{R}^2_+$ stay nonnegative and are uniformly bounded; in particular $\limsup_{t\to\infty} u(t) \le (r - d)/p$.
2. *(Equilibria.)* The extinction state $E_0$ is unstable. The predator-free state $E_1 = (\bar u, 0)$, $\bar u = (r - d)/p$, is locally asymptotically stable iff $(ca - \mu_1)(1-m)\bar u < \mu_1 s - ca\eta A$, and loses stability through a transcritical bifurcation at

    $$a_{TC_1} = \frac{\mu_1\{s + (1-m)\bar u\}}{c\{\eta A + (1-m)\bar u\}}.$$

    A prey-free state $E_2 = (0, \tilde v)$, sustained by the additional food, exists when $ca\eta A > \mu_1 s$ and is stable iff $\omega\{dl + a(1-m)\}\tilde v^2 + \{ds\omega + a(1-m) - (r-d)l\}\tilde v - (r - d)s > 0$, with a transcritical bifurcation where this expression vanishes.

3. *(Hopf.)* When the coexistence equilibrium $E^*$ is feasible and $\det J(E^*) > 0$, a simple Hopf bifurcation occurs at $\omega = \omega_H$, the unique positive root of $\operatorname{tr} J(E^*) = 0$, so increasing fear can switch the coexistence state between stable equilibrium and oscillation.
4. *(Turing instability, local model.)* If $E^* = (u^*, v^*)$ is stable for the ODE and the Jacobian $J = (a_{ij})$ at $E^*$ satisfies $d_2 a_{11} + d_1 a_{22} > 0$ and $(d_2 a_{11} + d_1 a_{22})^2 > 4d_1d_2\det J$, with $d_1 < d_2$, then $E^*$ is Turing unstable for every wavenumber $k^2$ in the interval between the roots of $d_1d_2k^4 - (d_2a_{11} + d_1a_{22})k^2 + \det J = 0$.

## Depends on

- [Linearly unstable Fourier mode](../../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode.md)

## Proof depends on

- [Mode instability iff the dispersion polynomial is negative](../../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/is-unstable-mode-iff-dispersion-det-neg.md)
- [Dispersion polynomial is negative exactly on the unstable band](../../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/dispersion-det-neg-iff.md)

## Expansion

Additional food lets predators persist without prey, which is why a prey-free equilibrium exists at all, while the refuge and fear both weaken predation and can stabilize or destabilize coexistence depending on parameters. The Turing condition is the standard one for two-species reaction–diffusion: a stable kinetic state destabilizes when the activator (prey, with $a_{11} > 0$ near $E^*$) diffuses more slowly than the inhibitor. In the nonlocal model the perceived predator density is a spatial average, which changes the effective cross-interaction at each wavenumber by the Fourier transform of $\phi_\delta$ and, numerically, produces patterns not seen in the local model.

## Sources

- Sangeeta Saha, Swadesh Pal and Roderick Melnik, "Analysis of the impact of fear in the presence of additional food and prey refuge with nonlocal predator–prey models", Ecological Modelling 505 (2025), 111103, <https://doi.org/10.1016/j.ecolmodel.2025.111103>; numbering as in arXiv:2310.01392: Section 2 (model and nonlocal extension), Theorems 3.1–3.5 and Appendix (proofs of boundedness and stability).
