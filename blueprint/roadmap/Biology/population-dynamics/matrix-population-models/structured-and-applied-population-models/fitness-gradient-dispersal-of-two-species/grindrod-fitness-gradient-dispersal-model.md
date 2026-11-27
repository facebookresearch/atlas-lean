# Grindrod's two-species fitness-gradient dispersal model

Let $\Omega \subset \mathbb{R}^2$ be a bounded domain with outer normal $n$. Two populations with densities $u_1, u_2 \ge 0$ disperse randomly and also advect up the gradient of a smoothed fecundity (projected net reproduction rate). In nondimensional form, for $i = 1, 2$,

$$
\partial_t u_i = r_i u_i E_i(x, u_1, u_2) + \delta_i \Delta u_i - \nabla \cdot (u_i \nabla \phi_i),
\qquad
-\varepsilon_i \Delta \phi_i + \phi_i = E_i(x, u_1, u_2),
$$

with linear fecundities

$$
E_1 = A_1(x) - a_1 u_1 - b_1 u_2 - d_1(x), \qquad E_2 = A_2(x) - a_2 u_1 - b_2 u_2 - d_2(x),
$$

where $r_i \ge 0$, $\delta_i \in (0,1)$ and $\varepsilon_i \ge 0$. Here $A_i \ge 0$ measures resource exploitation, $a_1, b_2 > 0$ are intraspecific crowding coefficients, $a_2, b_1$ are interspecific coefficients, and $d_i \ge 0$ are hazards. The advection velocity $w_i = \nabla \phi_i$ is a potential flow; $\varepsilon_i > 0$ smooths the fecundity gradient, and $\varepsilon_i = 0$ gives $w_i = \nabla E_i$.

Neumann conditions $n \cdot \nabla u_i = n \cdot \nabla \phi_i = 0$ on $\partial \Omega$ imply the no-flux condition $n \cdot (\delta_i \nabla u_i - u_i \nabla \phi_i) = 0$, so the total population changes only through the reaction terms.

With $A_1, a_1, b_1, b_2 > 0$, the sign pattern of the remaining parameters gives three interaction types:

- competition: $A_2 > 0$, $a_2 > 0$ (the species repel each other);
- generalist predator–prey (intraguild predation): $A_2 > 0$, $a_2 < 0$;
- predator–prey: $A_2 = 0$, $a_2 < 0$ (species 2 is attracted to species 1 and lives only on it).

## Expansion

Unlike chemotaxis or the cross-diffusion of Shigesada, Kawasaki and Teramoto, individuals respond directly to the local fitness landscape created by both populations. They need no separate attractant field. The elliptic equation for $\phi_i$ makes the advection nonlocal: each individual uses a blurred estimate of the fitness gradient. Restricting $w_i$ to gradients drops rotational parts of the general velocity equation $-\varepsilon_i \Delta w_i + w_i = \nabla E_i$, which agrees with it when $\varepsilon_i = 0$. The cases $A_1 = 0$ and $a_2 < 0$ make species 2 a predator that climbs the prey-density gradient, while the prey flees down the predator-density gradient, because $b_1 > 0$.

## Sources

- Kurowski L, Krause AL, Mizuguchi H, Grindrod P, Van Gorder RA. Two-species migration and clustering in two-dimensional domains. *Bulletin of Mathematical Biology* 79 (2017) 2302–2333. <https://doi.org/10.1007/s11538-017-0331-0>. PMCID: PMC5597722.
