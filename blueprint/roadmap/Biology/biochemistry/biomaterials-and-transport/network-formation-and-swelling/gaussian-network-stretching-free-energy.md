# Gaussian network stretching free energy

In the affine Gaussian network model, stretching a dry-referenced polymer network with principal stretches $\lambda_1, \lambda_2, \lambda_3$ costs $\tfrac12 NkT(\lambda_1^2+\lambda_2^2+\lambda_3^2 - 3 - 2\log\lambda_1\lambda_2\lambda_3)$ per unit dry volume; Panyukov's review writes the phantom-network form with stretches from the preparation state and modulus $kT\nu(1 - 2/f)$.

Affine model (Hong et al.). Let $N > 0$ be the number of polymer chains of the network divided by the volume of the dry polymer, and $\lambda_1, \lambda_2, \lambda_3 > 0$ the principal stretches of the deformation gradient $F$ from the dry, unstressed state. The stretching free energy per unit dry volume is

$$W_s(F) = \tfrac12 NkT\left(\lambda_1^2 + \lambda_2^2 + \lambda_3^2 - 3 - 2\log(\lambda_1\lambda_2\lambda_3)\right).$$

For an isochoric simple shear of the dry network this gives shear modulus $NkT$, the value Hong et al. state.

Phantom model (Panyukov's review). For a perfect, monodisperse phantom network of Gaussian strands, all junctions having the same functionality $f > 2$, Panyukov writes the elastic free energy per unit volume as quadratic in the stretches $\lambda_\alpha = L_\alpha/L_{0\alpha}$ of the network dimensions relative to the state of preparation,

$$F_{ph} = G\sum_{\alpha}\frac{\lambda_\alpha^{2} - 1}{2},$$

with modulus $G = kT\nu$ in the affine network model and

$$G = kT\nu\left(1 - \frac{2}{f}\right)$$

for the perfect phantom network, $\nu$ being the number concentration of network strands, so that $G$ has units of pressure and $F_{ph}$ is an energy density.

## Context

Graduate polymer physics (rubber elasticity). The two expressions are not interchangeable: they differ in reference state (dry state versus state of preparation), in volume normalization, in the volumetric term ($-2\log\det F$ appears only in the affine form above), and in the modulus. Panyukov notes that comparing his Eqs. (4) and (23) shows the perfect phantom network's modulus to be smaller than the affine one by the factor $1 - 2/f$.

## Depends on

None.

## Proof depends on

None.

## Expansion

Needed before theorem pages: the Gaussian end-to-end distribution of a long freely jointed chain and its entropy, summation over chains under affine deformation, the origin of the logarithmic term (Flory's volume-change correction), and, for the phantom form, the combined-chain (virtual-chain) argument behind Panyukov's Eq. (23).

## Sources

- W. Hong, X. Zhao, J. Zhou and Z. Suo, "A theory of coupled diffusion and large deformation in polymeric gels", Journal of the Mechanics and Physics of Solids 56, 1779–1793 (2008), <https://doi.org/10.1016/j.jmps.2007.11.010>; author-hosted copy read at <https://suo.seas.harvard.edu/sites/g/files/omnuum4271/files/suo/files/200.pdf>: Section 3, Eq. (21), and Section 5, which states the small-strain shear modulus $NkT$ and representative values $NkT = 10^4$–$10^7$ N/m²
- S. Panyukov, "Theory of Flexible Polymer Networks: Elasticity and Heterogeneities", Polymers 12(4), 767 (2020), <https://doi.org/10.3390/polym12040767>; open-access copy read at <https://www.mdpi.com/2073-4360/12/4/767>: Section 2: Eq. (1) (phantom free energy with stretches from the preparation state), Eq. (4) (affine modulus $G = kT\nu$) and Section 2.4 (monodisperse networks), Eqs. (20)–(23) (perfect phantom network, $G = kT\nu(1 - 2/f)$), with the sentence comparing (23) and (4)
