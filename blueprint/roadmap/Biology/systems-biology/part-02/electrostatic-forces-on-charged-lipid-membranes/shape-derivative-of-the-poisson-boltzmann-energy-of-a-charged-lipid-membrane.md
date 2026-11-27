# Shape derivative of the Poisson–Boltzmann energy of a membrane with mobile charged lipids

**Setting.** A domain $\Omega\subset\mathbb R^3$ is split into solvent $\Omega_s$, membrane $\Omega_m$ (a lipid bilayer bounded by surfaces $\Gamma_e,\Gamma_c$) and protein $\Omega_p$, with dielectric constants $\varepsilon_s,\varepsilon_m,\varepsilon_p$. Fixed charges have density $f$, $\chi_s$ is the indicator of the solvent, and the mobile ions contribute $B(\phi)=\beta^{-1}\sum_jc_j^\infty(e^{-\beta q_j\phi}-1)$, with $\beta=1/(k_BT)$. Charged lipids of charge $q_l$ are distributed on the membrane surfaces $\Gamma$ with density

$$\rho[\Gamma]=\frac{C\,\gamma'(\phi)}{\beta q_l\int_\Gamma\gamma(\phi)\,dS},$$

for a given smooth function $\gamma$ and constant $C$. With $\gamma(\phi)=-e^{-q_l\beta\phi}$ and $C=\int_\Gamma\rho\,dS$ the total number of charged lipids, $\rho$ is the Boltzmann distribution. This is the steady state of the surface electrodiffusion equation $\partial_t\rho=\nabla_s\cdot(D\nabla_s\rho+Dq_l\rho\nabla_s\phi)$.

**Theorem.**

1. *(Variational principle.)* Let

$$G[\Gamma;\phi]=\int_\Omega\Big[-\frac\varepsilon2|\nabla\phi|^2+f\phi-\chi_sB(\phi)\Big]d\Omega+\frac C\beta\ln\Big(\frac{\int_\Gamma\gamma(\phi)\,dS}{\int_\Gamma dS}\Big)$$

on $H^1_g(\Omega)=\{\phi\in H^1(\Omega):\phi=g\text{ on }\partial\Omega\}$. Then $G[\Gamma;\cdot]$ has a critical point $\psi_0$, its unique maximizer. This $\psi_0$ is the weak solution of the nonlinear Poisson–Boltzmann problem

$$\nabla\cdot(\varepsilon\nabla\phi)-\chi_sB'(\phi)=-f,\qquad \varepsilon_s\partial_n\phi^s=\varepsilon_m\partial_n\phi^m-\rho[\Gamma]q_l\ \text{on }\Gamma_e,\Gamma_c,$$

with continuity of $\phi$ across interfaces, flux continuity on the protein surface, and $\phi=g$ on $\partial\Omega$. Set $G[\Gamma]=G[\Gamma;\psi_0]$.
2. *(Surface transformation.)* Deform the membrane surfaces by a smooth velocity field $V$. The surface Jacobian $J_s$ satisfies $\frac{dJ_s}{dt}\big|_{t=0}=\nabla_s\cdot V$, and $\int_\Gamma\nabla_s\cdot F\,dS=0$ for continuous tangential fields $F$ on a closed surface.
3. *(Electrostatic force.)* If $f\in H^1(\Omega)$, the shape derivative of $G[\Gamma]$ in direction $V$ is

$$\delta_\Gamma G[\Gamma]=\int_\Gamma\Big(\frac{\varepsilon_s}{2}|\nabla\psi_0^s|^2-\frac{\varepsilon_m}{2}|\nabla\psi_0^m|^2+\varepsilon_m(\nabla\psi_0^m\cdot n)^2-\varepsilon_m(\nabla\psi_0^s\cdot n)(\nabla\psi_0^m\cdot n)+B(\psi_0)+q_l\rho[\Gamma](\nabla\psi_0^s\cdot n)\Big)(V\cdot n)\,dS.$$

By the Hadamard–Zolésio structure theorem it depends only on the normal component $V\cdot n$. The normal electrostatic force density $F_n$ on the charged membrane surface is defined by $\delta_\Gamma G[\Gamma]=-\int_\Gamma F_n\,(V\cdot n)\,dS$, so $F_n$ is minus the integrand above (the source's (3.14)–(3.15)).
4. *(Consistency.)* This $F_n$ equals the jump across the membrane surface of the normal component of the Maxwell stress tensor $M=\varepsilon E\otimes E-\frac\varepsilon2|E|^2I-\chi_sB(\psi)I$, where $E=-\nabla\psi$.

## Expansion

The logarithmic surface term is chosen so that its first variation is $\int_\Gamma\rho[\Gamma]q_l\psi\,dS$. This reproduces the jump condition created by the surface charge, so maximizing $G$ is equivalent to solving the Poisson–Boltzmann problem. The shape derivative is computed by pulling the energy back to the reference configuration with the flow of $V$. The volume Jacobian contributes $\nabla\cdot V$, the surface Jacobian contributes $\nabla_s\cdot V$, and the material derivative of $\psi_0$ drops out because $\psi_0$ is a critical point. The surface-divergence identity removes the tangential terms. The resulting force density can be coupled to elastic (Helfrich-type) membrane energies in electromechanical models of protein–membrane interactions, with the lipid distribution entering through the $q_l\rho\,\partial_n\psi^s$ term.

These are the variational theorem (Section 2), the surface-transformation theorem and lemma (Section 3.2), the shape-derivative theorem (Section 3.3) and the Maxwell-stress equivalence (Section 4) of the source.

## Sources

- M. Mikucki, Y. C. Zhou, "Electrostatic forces on charged surfaces of bilayer lipid membranes", arXiv:1301.1104 (2013). <https://doi.org/10.48550/arXiv.1301.1104>
