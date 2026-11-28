# Stokes–Einstein diffusivity of a sphere

In continuum theory, a dilute rigid sphere of hydrodynamic radius $r_s$ diffusing at long times in a liquid of viscosity $\eta$ at temperature $T$ has diffusion coefficient $D_0 = k_BT/(6\pi\eta r_s)$.

For a dilute tracer sphere of radius $r_s > 0$, much larger than the solvent molecules, undergoing Brownian motion at thermal equilibrium in an unbounded Newtonian liquid of viscosity $\eta > 0$ at absolute temperature $T > 0$, with no-slip creeping flow, the long-time translational diffusion coefficient is

$$D_0 = \frac{k_B T}{6\pi\eta r_s},$$

where $k_B$ is Boltzmann's constant. It combines the Einstein relation $D_0 = k_BT/\zeta$ with the Stokes friction coefficient $\zeta = 6\pi\eta r_s$.

## Context

Undergraduate physical chemistry. In hydrogel delivery it sets the free-solution diffusivity of a drug or nanoparticle. Li and Mooney report measured protein diffusivities of $10^{-11}$–$10^{-9}$ m²/s and estimate the time to diffuse out of a hydrogel of thickness $H$ as $H^2/D$, about 0.3–30 hours for $H = 1$ mm. Hong et al. use the formula only as an order-of-magnitude estimate for solvent molecules ($R = 3\times10^{-10}$ m, $\eta = 0.89\times10^{-3}$ Pa s gives $D \approx 8\times10^{-10}$ m²/s at room temperature), noting it was derived for particles much larger than molecules.

## Depends on

None.

## Proof depends on

None.

## Expansion

The proof needs two ingredients: (1) the Stokes drag law, that a rigid sphere of radius $r_s$ translating at speed $v$ through an unbounded Newtonian liquid in creeping flow with no slip feels the force $6\pi\eta r_s v$, from the creeping-flow (Stokes) solution around a sphere; and (2) the Einstein relation $D = k_BT/\zeta$ for an overdamped Brownian particle with friction coefficient $\zeta$, for example from the balance of diffusive and drift fluxes at Boltzmann equilibrium in an external potential, or from the long-time limit of Langevin dynamics. The Stokes settling-velocity balance takes the drag law as given and does not supply either ingredient.

## Sources

- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 5, the paragraph on the diffusion time scale: Stokes–Einstein formula and the water estimate
- Hydrogel Design, "Mesh Transport" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/mesh-transport/>: Stokes–Einstein equation for the free diffusion coefficient $D_0$ and the typical range 1–1000 µm²/s
- J. Li and D. J. Mooney, "Designing hydrogels for controlled drug delivery", Nature Reviews Materials 1, 16071 (2016), <https://doi.org/10.1038/natrevmats.2016.71>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC5898614/>: section "Mesh size controls diffusion and release": Stokes–Einstein equation (printed with $RT$), protein diffusivity range, and the diffusion-time estimate $H^2/D$ of about 0.3–30 hours for 1 mm
- E. Axpe, D. Chan, G. S. Offeddu, Y. Chang, D. Merida, H. Lopez Hernandez and E. A. Appel, "A Multiscale Model for Solute Diffusion in Hydrogels", Macromolecules 52, 6889–6897 (2019), <https://doi.org/10.1021/acs.macromol.9b00753>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6764024/>: Model Formulation, Eq. (1)
