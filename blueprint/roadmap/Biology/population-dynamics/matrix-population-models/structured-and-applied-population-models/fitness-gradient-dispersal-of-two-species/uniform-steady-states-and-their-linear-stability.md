# Uniform steady states of fitness-gradient dispersal and their linear stability

Consider the two-species fitness-gradient dispersal model on a bounded domain $\Omega \subset \mathbb{R}^2$ with Neumann conditions and spatially constant fecundities. Here $E_1 = A_1 - a_1 u_1 - b_1 u_2$ and $E_2 = A_2 - a_2 u_1 - b_2 u_2$, with $A_1, a_1, b_1, b_2 > 0$, $A_2 \ge 0$ and $a_2 \in \mathbb{R}$. Take $r_i > 0$, $\delta_i \in (0,1)$ and $\varepsilon_i \ge 0$, and assume that $\varepsilon_i^{-1}$ is not a Neumann eigenvalue of $-\Delta$.

**Uniform steady states.** The spatially uniform steady states $(u_1^*, u_2^*, \phi_1^*, \phi_2^*)$ are

$$
(0,0,A_1,A_2), \quad \Big(0, \tfrac{A_2}{b_2}, A_1 - \tfrac{b_1 A_2}{b_2}, 0\Big), \quad \Big(\tfrac{A_1}{a_1}, 0, 0, A_2 - \tfrac{a_2 A_1}{a_1}\Big),
$$

$$
\Big(\tfrac{A_1 b_2 - A_2 b_1}{a_1 b_2 - a_2 b_1}, \tfrac{A_2 a_1 - A_1 a_2}{a_1 b_2 - a_2 b_1}, 0, 0\Big) \quad (a_1 b_2 \ne a_2 b_1).
$$

The coexistence state is positive exactly under these conditions (Theorem 1):

- competition ($a_2, A_2 > 0$): $b_1/b_2 < A_1/A_2 < a_1/a_2$ or $a_1/a_2 < A_1/A_2 < b_1/b_2$;
- generalist predator–prey ($A_2 > 0 > a_2$): $b_1/b_2 < A_1/A_2$;
- predator–prey ($A_2 = 0 > a_2$): always.

**Linear stability (Theorems 2–5).** Consider perturbations proportional to $e^{\eta t + i k \cdot x}$, where $|k|^2$ ranges over the Neumann spectrum, which always contains $k = 0$.

1. The extinction state $(0,0)$ is always linearly unstable.
2. The state $(0, A_2/b_2)$ with $A_2 > 0$ is linearly stable if $A_1 < (b_1/b_2) A_2$.
3. The state $(A_1/a_1, 0)$ is linearly stable if $A_2 < (a_2/a_1) A_1$.
4. A feasible coexistence state is linearly stable if $a_1 b_2 - a_2 b_1 > 0$ and unstable if $a_1 b_2 - a_2 b_1 < 0$.

These are exactly the stability conditions of the corresponding equilibria of the nonspatial Lotka–Volterra kinetics $\dot u_i = r_i u_i (A_i - a_i u_1 - b_i u_2)$ (Theorem 6). Fitness-gradient dispersal therefore produces no diffusion- or taxis-driven instability of uniform states.

## Depends on

- [Grindrod's two-species fitness-gradient dispersal model](grindrod-fitness-gradient-dispersal-model.md)
- [Turing instability](../../../../pattern-formation/turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Linearizing and eliminating $\hat\phi_i = -(a_i \hat u_1 + b_i \hat u_2)/(1+\varepsilon_i k^2)$, with the appropriate coefficients, gives a $2 \times 2$ dispersion problem. On a boundary state it factors: for $(0, A_2/b_2)$ one branch is $\eta = (A_1 - b_1 A_2 / b_2)(r_1 + k^2) - \delta_1 k^2$. The minimum over $k$ of the threshold $\delta_1 k^2/(r_1 + k^2)$ is attained at $k = 0$, which gives the kinetic condition. For the coexistence state the dispersion relation is $\eta^2 + \xi_1(k)\eta + \xi_0(k) = 0$. Here $\xi_1(k) > 0$, and $\xi_0(k)$ equals $(a_1 b_2 - a_2 b_1) u_1^* u_2^*$ at $k = 0$, plus terms that are nonnegative when $a_1, b_2 > 0$. So the sign of $a_1 b_2 - a_2 b_1$ decides stability at every wavenumber. The argument uses only that $k = 0$ is the bottom of the Neumann spectrum. The paper's numerics show that persistent spatial clustering instead comes from heterogeneous resources $A_i(x)$ or hazards $d_i(x)$, or from non-convex domains.

## Sources

- Kurowski L, Krause AL, Mizuguchi H, Grindrod P, Van Gorder RA. Two-species migration and clustering in two-dimensional domains. *Bulletin of Mathematical Biology* 79 (2017) 2302–2333. <https://doi.org/10.1007/s11538-017-0331-0>. PMCID: PMC5597722.
