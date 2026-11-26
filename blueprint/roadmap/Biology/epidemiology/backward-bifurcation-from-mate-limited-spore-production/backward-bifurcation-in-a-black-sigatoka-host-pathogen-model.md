# Backward bifurcation in a Black Sigatoka host–pathogen model

**Model.** Healthy leaf biomass $H$ and partially resistant biomass $R$ (fraction $1-\kappa$ of new biomass, susceptibility reduced by $\delta$), exposed $E$ and infected $I$ biomass, asexual spores (conidia) $A$ and sexual spores (ascospores) $S$:
$$\begin{aligned}
\dot H &= \kappa\Lambda - \beta\bigl(\theta S + \psi \tfrac{A}{N}\bigr) H - \mu H, & \dot R &= (1-\kappa)\Lambda - (1-\delta)\beta\bigl(\theta S + \psi\tfrac{A}{N}\bigr) R - \mu R,\\
\dot E &= \beta\bigl(\theta S + \psi\tfrac{A}{N}\bigr)\bigl(H + (1-\delta) R\bigr) - (\gamma + \mu) E, & \dot I &= \gamma E - (\mu + \rho) I,\\
\dot A &= \eta I - (\mu_P + \rho) A, & \dot S &= \alpha\, g(I)\, I - (\mu_P + \rho) S,
\end{aligned}$$
where $\beta = \beta(h, T)$ depends on humidity and temperature, $\rho$ is the removal (sanitation) rate, and the mating function $g$ satisfies $g(I) \sim \lambda I$ as $I \to 0$ (mate limitation of sexual reproduction).

**Theorem.**
1. Since ascospore production is quadratic in $I$ near the disease-free state, only conidia enter the basic reproduction number:

$$\mathcal R_0 = \frac{\beta\,\psi\,\eta\,\gamma\,[\delta\kappa + (1 - \delta)]}{(\gamma + \mu)(\mu_P + \rho)(\mu + \rho)} .$$

2. Let $a$ and $b$ be the center-manifold bifurcation coefficients at $\mathcal R_0 = 1$ (transmission parameter $\beta_0 = \beta_0^*$). The model undergoes a backward bifurcation at $\mathcal R_0 = 1$ when $a > 0$, $b > 0$ and the mating-efficiency parameter exceeds an explicit threshold, $\lambda > \lambda^{\mathrm{crit}}$. Then a stable endemic equilibrium coexists with the stable disease-free equilibrium for $\mathcal R_0 < 1$.

## Expansion

At low infected biomass the two mating types rarely meet, so sexual spores scale like $I^2$ and contribute nothing to invasion, but at moderate infection they add a positive feedback that the linearisation misses. The Castillo-Chavez–Song center-manifold theorem turns this into the sign of $a$, which becomes positive when the ascospore pathway is strong enough ($\lambda > \lambda^{\mathrm{crit}}$). Consequently, driving $\mathcal R_0$ just below one by fungicide or sanitation does not eliminate an established epidemic, which explains the persistence of the disease and the need to reduce $\mathcal R_0$ well below the threshold; stochastic simulations confirm the bistability.

## Sources

- B. A. Afful, L. F. Gordillo, "The Curse of Black Sigatoka: A Backward Bifurcation Perspective", arXiv:2604.26060 (2026), model (Section 2), basic reproduction number (Section 3) and Theorem 1, <https://doi.org/10.48550/arXiv.2604.26060>.
