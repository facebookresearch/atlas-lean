# Free energy identity for electrodiffusion with osmotic water flow and membrane capacitance

**Model.** Take the setting of solute diffusion with osmotic water flow across a deformable hyperelastic membrane $\Gamma$ (intracellular $\Omega_i$, extracellular $\Omega_e$), now with ions of valence $z_k$. The chemical potential becomes

$$
\mu_k=\frac{\partial\omega}{\partial c_k}+qz_k\phi ,
$$

so the bulk equation $\partial_tc_k+\nabla\cdot(\mathbf uc_k)=\nabla\cdot(c_k\frac{D_k}{k_BT}\nabla\mu_k)$ is a Nernst–Planck equation with advection. The potential $\phi$ solves the Poisson equation $-\nabla\cdot(\epsilon\nabla\phi)=\sum_kqz_kc_k$ with constant $\epsilon$, Neumann data on $\partial\Omega$, and the capacitor condition on the membrane

$$
-\epsilon\,\partial_{\mathbf n}\phi\big|_{\Gamma_i}=-\epsilon\,\partial_{\mathbf n}\phi\big|_{\Gamma_e}=C_m[\phi].
$$

The fluid obeys Stokes flow with the electrostatic body force, written through the Maxwell stress $\Sigma_e(\phi)$; force balance on the membrane reads

$$
[(\Sigma_m(\mathbf u,p)+\Sigma_e(\phi))\mathbf n]=\mathbf F_{\mathrm{elas}}+\mathbf F_{\mathrm{cap}},\qquad \mathbf F_{\mathrm{cap}}=\tau_{\mathrm{cap}}\kappa_\Gamma\mathbf n-\nabla_\Gamma\tau_{\mathrm{cap}},\quad \tau_{\mathrm{cap}}=\tfrac12\Big(C_m+Q\frac{\partial C_m}{\partial Q}\Big)[\phi]^2,
$$

with $\kappa_\Gamma$ the sum of principal curvatures, $\nabla_\Gamma$ the surface gradient and $Q$ the areal stretch of the membrane relative to its reference configuration. The passive ion fluxes satisfy $[\mu_k]j_k\ge 0$ (they may now depend on the membrane potential $[\phi]$), and the solute flux, osmotic slip $\mathbf u-\partial_t\mathbf X=j_w\mathbf n$ and water-flux conditions $[\widehat{\psi_w}]j_w\ge0$ are as in the uncharged case.

**Theorem (electro-osmotic free energy identity).** Smooth solutions satisfy

$$
\frac{d}{dt}\big(G_S+E_{\mathrm{elas}}+E_{\mathrm{elec}}\big)=-I_p-J_p-J_a,\qquad E_{\mathrm{elec}}=\int_{\Omega_i\cup\Omega_e}\tfrac12\epsilon|\nabla\phi|^2d\mathbf x+\int_\Gamma\tfrac12C_m[\phi]^2dm_\Gamma,
$$

with $G_S$, $E_{\mathrm{elas}}$, the bulk dissipation $I_p$, the passive membrane dissipation $J_p$ and the active term $J_a$ defined exactly as in the uncharged identity. The same identity holds for an area-incompressible membrane ($Q\equiv1$) if the capacitive force is replaced by a surface pressure $\lambda\kappa_\Gamma\mathbf n-\nabla_\Gamma\lambda$ with Lagrange multiplier $\lambda$. Without active fluxes the total free energy is nonincreasing.

**Limiting energy laws.** After nondimensionalization, the zero-Péclet limit (no flow, fixed membrane) satisfies $\frac{d}{dt}(G_S+E_{\mathrm{elec}})=-F_c-J_a$, with $F_c$ the resulting chemical dissipation, and the electroneutral limit satisfies $\frac{d}{dt}(G_S+E_{\mathrm{elas}})=-I_p-J_p-J_a$.

## Expansion

Compared with the uncharged calculation, testing the Nernst–Planck equations with $\mu_k$ produces the extra term $\int qz_k\phi\,\partial_tc_k$, which the time derivative of the Poisson equation converts into $\frac{d}{dt}$ of the bulk field energy plus membrane terms. Because the membrane moves and stretches, the capacitor energy $\frac12C_m[\phi]^2$ changes with geometry; the capacitive force is exactly the surface tension of strength $-\tau_{\mathrm{cap}}$ needed to absorb that change, so the proof doubles as a variational derivation of $\mathbf F_{\mathrm{cap}}$. The Maxwell stress in the force balance accounts for the electrostatic body force on the fluid. The resulting thermodynamically consistent framework underlies cell-volume and membrane-potential models in which pumps (the $a_k$) maintain a nonequilibrium steady state.

## Depends on

- [Free energy identity for solute diffusion and osmotic water flow across a moving membrane](free-energy-identity-for-solute-diffusion-and-osmotic-water-flow.md)
- [One-dimensional Nernst–Planck flux](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-planck-flux.md)

## Sources

- Y. Mori, C. Liu, R. S. Eisenberg, "A Model of Electrodiffusion and Osmotic Water Flow and its Energetic Structure" (2011), Section 3 (Theorem 3.1) and Section 4 (the two energy-equality propositions, 4.1 and 4.2). <https://doi.org/10.48550/arXiv.1101.5193>
