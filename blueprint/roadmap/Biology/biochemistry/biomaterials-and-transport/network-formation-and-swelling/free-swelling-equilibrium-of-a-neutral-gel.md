# Free-swelling equilibrium of a neutral gel (Flory–Rehner)

In the Flory–Rehner model an unloaded neutral gel in pure solvent swells until the solvent chemical potential vanishes; for a dry-formed affine network this fixes the isotropic stretch $\lambda$ through one equation in $Nv$ and $\chi$.

Take the free energy per unit dry volume $W = W_s + W_m$ (affine stretching plus Flory–Huggins mixing, pages linked below), molecular incompressibility $1 + vC = \det F$, and solvent chemical potential $\mu = \partial W/\partial C + Pv$ with osmotic pressure $P$. For a gel formed in the dry state, unloaded (all nominal stresses zero) and in equilibrium with pure liquid solvent ($\mu = 0$), deforming isotropically with stretch $\lambda > 1$ so that $1 + vC = \lambda^3$, the stretch satisfies

$$\log\left(1 - \lambda^{-3}\right) + \lambda^{-3} + \chi\,\lambda^{-6} + Nv\left(\lambda^{-1} - \lambda^{-3}\right) = 0 .$$

Equivalently, with $\phi = \lambda^{-3}$, $\ln(1-\phi) + \phi + \chi\phi^2 + Nv(\phi^{1/3} - \phi) = 0$. For $Nv = 10^{-3}$ and $\chi = 0.2$, Hong et al. report the free-swelling stretch 3.215; this is a property of the model, not a statement about real gels.

For networks formed at polymer fraction $\phi_0$ in solution, with junction functionality $f > 2$ and chain-end defect fraction $\gamma$, Richbourg, Ravikumar and Peppas use the separate phantom-network equation

$$\frac{\ln(1-\phi_s) + \phi_s + \chi\phi_s^2}{\phi_s^{1/3}} = -\left(1 - \frac{2}{f}\right)(1-\gamma)\,\frac{V_1\rho_d}{M_r N_j}\,\phi_0^{2/3}, \qquad 0 < \phi_s < 1,$$

with $V_1$ the solvent molar volume, $\rho_d$ the dry polymer density, $M_r$ the repeat-unit molar mass and $N_j$ the degree of polymerization between junctions.

## Context

Graduate. The equilibrium polymer fraction feeds mesh size, modulus and diffusivity estimates. Assumptions: additive elastic and mixing free energies; Gaussian chains without entanglements or finite extensibility; constant $\chi$ (the Hydrogel Design notes call its equality with the free-polymer value assumed but unproven); no ions. The two equations are distinct models (different reference states and elastic terms) and should not be mixed. Muñoz Taboada et al. (2024) list low swelling among the design requirements of a gastrointestinal sealant; neither equation was fitted to that material.

## Depends on

- [Gaussian network stretching free energy](gaussian-network-stretching-free-energy.md)
- [Flory–Huggins mixing free energy of a swollen network](flory-huggins-mixing-free-energy-of-a-swollen-network.md)

## Proof depends on

None.

## Expansion

Derivation: zero stress gives $P = NkT(\lambda^{-1} - \lambda^{-3})$; substituting into $\mu = kT[\log(1 - \lambda^{-3}) + \lambda^{-3} + \chi\lambda^{-6}] + Pv = 0$ gives the equation. For existence and uniqueness of a root $\phi \in (0,1)$ when $Nv > 0$ and $\chi < 1/2$, the left side $g$ is not monotone ($g' > 0$ near $0$ and $g' < 0$ near $1$), so a monotonicity argument fails; a workable route writes $-[\ln(1-\phi) + \phi + \chi\phi^2]/\phi^2 = \tfrac12 - \chi + \sum_{n \ge 3}\phi^{n-2}/n$ and compares it with $Nv(\phi^{1/3} - \phi)/\phi^2$, using that $\phi^{5/3}/(1 - \phi^{2/3})$ is increasing. The behaviour of the root as $Nv \to 0$, which depends on whether $\chi \le 1/2$, also needs a lemma; a numerical solve of the displayed equation reproduces 3.215 for the source's parameters. The phantom equation needs its own derivation from a free energy with formation-state reference, which the cited pages state without proof.

## Sources

- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 3, Eqs. (16)–(24) (incompressibility, stresses, chemical potential, free-energy function and equations of state); Section 6, Eq. (32) and the sentence specializing it to unconstrained swelling with $Nv = 10^{-3}$, $\chi = 0.2$ and equilibrium stretch 3.215
- N. R. Richbourg, A. Ravikumar and N. A. Peppas, "Solute Transport Dependence on 3D Geometry of Hydrogel Networks", Macromolecular Chemistry and Physics (2021), <https://doi.org/10.1002/macp.202100138>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC8389770/>: Eq. (1) and the definitions following it
- Hydrogel Design, "Equilibrium Swelling" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/equilibrium-swelling-theory/>: the displayed equilibrium swelling equation and the parameter notes on $\chi$, $f$, $\gamma$ and the bounds $0 < \phi_s < 1$, $\phi_0 < 0.5$
- G. Muñoz Taboada, D. Dahis, P. Dosta, E. Edelman and N. Artzi, "Sprayable Hydrogel Sealant for Gastrointestinal Wound Shielding", Advanced Materials 36, 2311798 (2024), <https://doi.org/10.1002/adma.202311798>; open-access accepted copy read at <https://par.nsf.gov/servlets/purl/10540642>: Section 2.1: design requirements including low swelling
