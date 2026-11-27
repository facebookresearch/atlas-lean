# Hopf bifurcation of the oncolytic virus kinetic model

**Model.** Let $C$, $I$ and $V$ be the nondimensional densities of uninfected tumour cells, infected tumour cells and free virus. The spatially homogeneous (kinetic) oncolytic virus model is

$$\dot C = C(1 - C - I) - CV, \qquad \dot I = CV - aI, \qquad \dot V = \theta I - \gamma V,$$

with $a, \gamma > 0$ (scaled death rate of infected cells and viral clearance rate) and the effective viral production rate $\theta > 0$ as bifurcation parameter. It is the kinetic part of the reaction–diffusion system $C_t = D_c\Delta C + \dots$, $I_t = D_i \Delta I + \dots$, $V_t = \Delta V + \dots$ with homogeneous Neumann boundary conditions.

**Steady states.** $E_0 = (0,0,0)$, $E_1 = (1,0,0)$ and, for $\theta > a\gamma$, the coexistence state

$$E_+ = (C^*, I^*, V^*) = \left(\frac{a\gamma}{\theta},\ \frac{\gamma(1 - C^*)}{\theta + \gamma},\ \frac{\theta(1 - C^*)}{\theta + \gamma}\right),$$

which arises by a transcritical bifurcation at $\theta_t = a\gamma$. The basic reproduction number of the virus is $R_0 = \theta/(a\gamma)$.

**Proposition.**

1. If $R_0 \le 1$, the nonnegative steady states are $E_0$, a saddle, and $E_1$, locally asymptotically stable.
2. If $R_0 > 1$, $E_0$ and $E_1$ are saddles and $E_+$ lies in the positive orthant.
3. $E_+$ is locally asymptotically stable if $\theta > \theta_t$ and $\kappa(\theta) > 0$, where

$$\kappa(\theta) = -\theta^3 + m\theta^2 + \gamma m\theta + a\gamma^3, \qquad m = (a+\gamma)^2 + a(\gamma + 1).$$

4. $\kappa$ has a unique positive root $\theta_H > \theta_t$, and the system undergoes a Hopf bifurcation at $\theta = \theta_H$: for $\theta > \theta_H$ the coexistence state loses stability to oscillations.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

The characteristic polynomial of the Jacobian at $E_+$ is $\lambda^3 + P_2\lambda^2 + P_1\lambda + P_0$ with $P_2 = C^* + a + \gamma$, $P_1 = C^*\bigl(a + \gamma + \theta(1 - C^*)/(\theta + \gamma)\bigr)$ and $P_0 = \theta C^*(1 - C^*)$, all positive for $0 < C^* < 1$. By Routh–Hurwitz, stability reduces to $H(\theta) = P_2 P_1 - P_0 > 0$, and substituting $C^* = a\gamma/\theta$ gives $H(\theta) = \frac{a\gamma}{\theta^2(\theta + \gamma)}\kappa(\theta)$. Descartes' rule of signs gives $\kappa$ exactly one positive root, and since $\kappa$ has negative leading coefficient, $\kappa < 0$ beyond it. The derivative $dH/d\theta$ is $-a\gamma$ times a polynomial with positive coefficients over a positive denominator, so it never vanishes, and Liu's criterion ($H(\theta_H) = 0$, $H'(\theta_H) \ne 0$, $P_0 \ne 0$) yields the Hopf bifurcation. In the spatial model these kinetic oscillations generate hollow-ring, target and dispersed infection patterns; the hollow ring is the pattern associated with tumour eradication.

## Sources

- A. A. Baabdulla and T. Hillen, "Oscillations in a Spatial Oncolytic Virus Model", *Bulletin of Mathematical Biology* (2024), <https://doi.org/10.1007/s11538-024-01322-z> (Section 3.1, system (5), Equation (6) and Proposition 3.1, numbered as in the preprint version <https://doi.org/10.1101/2023.12.19.572433>).
