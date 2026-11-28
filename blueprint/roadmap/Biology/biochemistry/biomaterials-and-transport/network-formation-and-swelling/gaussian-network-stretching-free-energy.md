# Gaussian network stretching free energy

In the affine Gaussian network model, stretching a dry-referenced polymer network with principal stretches $\lambda_1, \lambda_2, \lambda_3$ costs $\tfrac12 NkT(\lambda_1^2+\lambda_2^2+\lambda_3^2 - 3 - 2\log\lambda_1\lambda_2\lambda_3)$ per unit dry volume; the phantom model uses a different, separately normalized form.

Affine model (Hong et al.). Let $N > 0$ be the number of polymer chains of the network divided by the volume of the dry polymer, and $\lambda_1, \lambda_2, \lambda_3 > 0$ the principal stretches of the deformation gradient $F$ from the dry, unstressed state. The stretching free energy per unit dry volume is

$$W_s(F) = \tfrac12 NkT\left(\lambda_1^2 + \lambda_2^2 + \lambda_3^2 - 3 - 2\log(\lambda_1\lambda_2\lambda_3)\right).$$

For an isochoric simple shear of the dry network this gives shear modulus $NkT$, the value Hong et al. state.

Phantom model (Erman and Mark, as summarized by Hydrogel Design). For a network whose junctions of functionality $f > 2$ fluctuate freely, the elastic Helmholtz free energy of the sample is

$$\Delta A_{el,ph} = \tfrac12\left(1 - \frac{2}{f}\right)\nu_e k_B T\,(I_1 - 3), \qquad I_1 = \lambda_1^2 + \lambda_2^2 + \lambda_3^2,$$

with $\nu_e$ the number of elastically effective chains in the sample and stretches measured from that model's reference state.

## Context

Graduate polymer physics (rubber elasticity). The two expressions are not interchangeable: they differ in normalization (per dry volume versus per sample), in reference state, and in the volumetric term ($-2\log\det F$ is absent from the phantom form). Only for isochoric deformations from the same reference and the same chain density can the prefactors be compared, giving the factor $1 - 2/f$; for volume-changing deformations such as swelling the energies are not constant multiples, and one cannot be substituted for the other in a swelling balance.

## Depends on

None.

## Proof depends on

None.

## Expansion

Needed before theorem pages: the Gaussian end-to-end distribution of a long freely jointed chain and its entropy, summation over chains under affine deformation, the origin of the logarithmic term (Flory's volume-change correction), and, for the phantom form, the James–Guth junction-fluctuation argument. A lemma computing the small-strain shear modulus of each form for an isochoric shear would make the $1 - 2/f$ comparison precise.

## Sources

- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 3, Eq. (21), and Section 5, which states the small-strain shear modulus $NkT$ and representative values $NkT = 10^4$–$10^7$ N/m²
- Hydrogel Design, "Rubberlike Elasticity" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/rubberlike-elasticity-theory/>: history section: Flory's affine tension, the Peppas–Merrill update, and the Erman–Mark phantom free energy with the factor $1 - 2/f$
