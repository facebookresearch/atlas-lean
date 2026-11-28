# Shear modulus of a swollen network

For an affine Gaussian network formed at polymer fraction $\phi_r$ and swollen to $\phi_s$, the uniaxial engineering stress is $\tau = G(\alpha - \alpha^{-2})$ with $G = RT(1 - 2M_c/M_n)(\rho_d/(M_rN_j))\phi_r^{2/3}\phi_s^{1/3}$.

Let a network with degree of polymerization $N_j$ between junctions (repeat-unit molar mass $M_r$, $M_c = M_r N_j$), primary-chain number-average molar mass $M_n > 2M_c$ and dry density $\rho_d$ be formed at relaxed polymer volume fraction $\phi_r$ and swollen to $\phi_s$. Under incompressible uniaxial extension by ratio $\alpha > 0$ from the swollen state at fixed solvent content, the engineering stress (per unit swollen, unstretched area) is

$$\tau = G\left(\alpha - \frac{1}{\alpha^2}\right), \qquad G = RT\left(1 - \frac{2M_c}{M_n}\right)\frac{\rho_d}{M_r N_j}\,\phi_r^{2/3}\phi_s^{1/3} .$$

For a network formed dry ($\phi_r = 1$) this is Flory's form; without solvent and without the chain-end factor it reduces to the dry small-strain modulus $NkT$ of the affine stretching energy.

## Context

Graduate. The displayed form is taken from the Hydrogel Design model page (which restates Peppas and Merrill's Eqs. (5)–(6)); Panyukov's review gives the underlying affine and phantom moduli in the preparation state. The factor $1 - 2M_c/M_n$ is Flory's count of elastically effective chains for networks made by crosslinking long precursors; it is a model correction, not part of the affine stress derivation, and it is meaningless for end-linked networks or when $M_n \le 2M_c$. Junctions are assumed tetrafunctional. Inverting a measured modulus for $N_j$ requires a shear modulus measured at small strain under these assumptions; a compression Young's modulus of a gel needs a justified constitutive and test-regime conversion first.

## Depends on

- [Gaussian network stretching free energy](gaussian-network-stretching-free-energy.md)

## Proof depends on

None.

## Expansion

Derivation route: relative to the formation state the swollen gel is isotropically stretched by $\lambda_0 = (\phi_r/\phi_s)^{1/3}$; the molar density of strands per unit swollen volume is $(\rho_d/(M_rN_j))\phi_s$ (times the chain-end factor), so that multiplying by $RT$ gives a pressure; an affine Gaussian network then gives true stress $\propto \lambda_0^2$ per swollen volume, i.e. $G \propto \phi_s\,(\phi_r/\phi_s)^{2/3} = \phi_r^{2/3}\phi_s^{1/3}$, and uniaxial incompressible extension by $\alpha$ gives the factor $\alpha - \alpha^{-2}$ in engineering stress. Each step, and the separate chain-end correction, needs its own page; the formation-state stretch must not be confused with the dry-to-swollen stretch $\phi_s^{-1/3}$.

## Sources

- Hydrogel Design, "Rubberlike Elasticity" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/rubberlike-elasticity-theory/>: history section: Flory's tension from *Principles of Polymer Chemistry* (1953), chapter 11 appendix B, its translation to a neo-Hookean shear modulus, and the Peppas–Merrill (1977) equation in modulus form with $\phi_r^{2/3}\phi_s^{1/3}$, with its tetrafunctional and chain-end assumptions
- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 5: small-strain shear modulus $NkT$ of the dry network
- N. A. Peppas and E. W. Merrill, "Crosslinked poly(vinyl alcohol) hydrogels as swollen elastic networks", Journal of Applied Polymer Science 21, 1763–1770 (1977), <https://doi.org/10.1002/app.1977.070210704>: cited through the Hydrogel Design page; equations not read in the original
- S. Panyukov, "Theory of Flexible Polymer Networks: Elasticity and Heterogeneities", Polymers 12(4), 767 (2020), <https://doi.org/10.3390/polym12040767>; open-access copy read at <https://www.mdpi.com/2073-4360/12/4/767>: Section 2, Eqs. (1), (4) and (23): free energy with stretches from the preparation state and the affine and perfect-phantom moduli of a network of Gaussian strands; it does not display the swollen-state factor $\phi_r^{2/3}\phi_s^{1/3}$, for which the page relies on the model page above
