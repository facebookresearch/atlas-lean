# Global stability of the infected equilibrium in the activation-status structured HIV model

In the [activation-status structured HIV model](reproduction-number-threshold-of-the-activation-status-structured-hiv-model.md) with cell-free and cell-to-cell transmission and status switching kernel $\gamma(y, x)$ satisfying $\gamma(x, x) > 0$, suppose $R_0 = \rho(L) > 1$. Then the infected equilibrium $E^* = (H^*, I^*(\cdot), V^*)$ is **unique and globally asymptotically stable** in the interior of the state space $X_+ = \mathbb{R}_+ \times C_+([0, 1]) \times \mathbb{R}_+$.

**Lyapunov functional.** Let $\kappa(a) = a - 1 - \ln a \ge 0$, with equality only at $a = 1$, and set

$$\psi(x, y) = \big[\beta(x)\eta(y)(1 - \xi) k_2 H^* + d\, \gamma(y, x)\big] I^*(y) + d\, \beta(x)(1 - \epsilon(y)) k_1 H^* I^*(y), \qquad x, y \in [0, 1].$$

Since $\psi$ is continuous with $\psi(x, x) > 0$, there is a nonnegative Borel weight $w$ on $[0, 1]$ (Thieme 2011, Proposition 11.1) such that $w(x)\int_0^1 \psi(x, y)\, dy$ is integrable and

$$\int_0^1 w(x)\int_0^1 \psi(x, y)\big[\nu(x) - \nu(y)\big]\, dy\, dx = 0 \qquad \text{for all } \nu \in L^\infty([0, 1]).$$

With this weight,

$$\mathcal G(t) = \int_0^1 w(x)\left[d H^* \beta(x)\, \kappa\!\left(\frac{H}{H^*}\right) + d\, I^*(x)\, \kappa\!\left(\frac{I(t, x)}{I^*(x)}\right) + (1 - \xi) k_2 H^* V^* \beta(x)\, \kappa\!\left(\frac{V}{V^*}\right)\right] dx$$

satisfies $\dot{\mathcal G} \le 0$ along solutions, with equality only at $E^*$.

## Depends on

- [Reproduction number threshold of the activation-status structured HIV model](reproduction-number-threshold-of-the-activation-status-structured-hiv-model.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

When $R_0 > 1$, solutions starting off the infection-free set are strictly positive (by comparison with the pure switching–death semigroup) and uniformly weakly persistent. Together with dissipativity and asymptotic compactness, this gives a global attractor $Y$ in the interior, on which $H$, $I(\cdot)$ and $V$ are bounded away from $0$ and $\infty$, so $\mathcal G$ is well defined on complete orbits in $Y$. Differentiating, $\dot{\mathcal G}$ splits into $-\int w\, d\beta\, (1 - H^*/H)(cH - cH^*)$, several terms of the form $-(\text{positive}) \times \kappa(\cdot)$ for the cell-free, cell-to-cell, switching and viral-production fluxes, and one remaining term. That remaining term is $\int w \int \psi(x, y)\,[\nu(x) - \nu(y)]$ with $\nu = \ln(I/I^*) - I/I^*$, and it vanishes by the choice of $w$. Hence $\dot{\mathcal G} \le 0$, and LaSalle's principle yields $Y = \{E^*\}$, which also gives uniqueness of $E^*$.

## Sources

- Guo T, Qiu Z, Shen M, Rong L. Dynamics of a new HIV model with the activation status of infected cells. *Journal of Mathematical Biology* 82(6):51 (2021), Theorem 5 with equations (8)–(10), Appendix B (Theorems 6–9 on positivity and uniform persistence), Appendix C. <https://doi.org/10.1007/s00285-021-01604-3> (PMCID: PMC8049625)
