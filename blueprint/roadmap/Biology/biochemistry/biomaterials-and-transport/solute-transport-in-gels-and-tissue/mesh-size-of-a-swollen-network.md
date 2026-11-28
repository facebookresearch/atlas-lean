# Mesh size of a swollen network

In the Peppas group's model the mesh size $\xi$ is the root-mean-square distance between neighbouring junctions of a swollen network: the unperturbed end-to-end length of a network chain, multiplied by the isotropic swelling factor $\phi_s^{-1/3}$.

For a network with junction functionality $f > 2$, degree of polymerization $N_j$ between junctions, $\lambda$ backbone bonds of mean length $\bar l$ per repeat unit and Flory characteristic ratio $C_\infty$, swollen to polymer volume fraction $\phi_s \in (0,1)$, Richbourg, Ravikumar and Peppas define

$$\xi = \phi_s^{-1/3}\left[\left(1 - \frac{2}{f}\right)\bar l^{2} C_\infty \lambda N_j\right]^{1/2} .$$

A different, mechanical length is obtained from the shear modulus $G$ of the swollen gel via classical rubber elasticity (Li and Mooney, Box 1):

$$r_{mesh} = \left(\frac{6RT}{\pi N_{Av} G}\right)^{1/3} = \left(\frac{6k_BT}{\pi G}\right)^{1/3},$$

which corresponds to one elastic chain per sphere of diameter $r_{mesh}$; despite its notation it is a diameter-like length, not the portal radius of the [mesh radius](mesh-radius-of-regular-lattice-networks.md) page.

## Context

Graduate. Typical hydrogel mesh sizes are 5–100 nm (Li and Mooney), to be compared like with like: hydrodynamic diameters of 4.1 nm for lysozyme and 10.7 nm for IgG against diameter-like lengths, radii against radii. For PEG the Hydrogel Design values are $\bar l = 0.15$ nm, $C_\infty = 4$, $\lambda = 3$. Canal and Peppas (1989) introduced a regime-dependent correlation between mesh size and equilibrium polymer fraction; the factor $1 - 2/f$ is the later phantom-network correction. If a relaxed (formation) state at fraction $\phi_r$ is used as reference, lengths scale by $(\phi_r/\phi_s)^{1/3}$ instead of $\phi_s^{-1/3}$. Real networks have a distribution of mesh sizes, which a scalar $\xi$ does not describe.

## Depends on

- [Free-swelling equilibrium of a neutral gel (Flory–Rehner)](../network-formation-and-swelling/free-swelling-equilibrium-of-a-neutral-gel.md)
- [Shear modulus of a swollen network](../network-formation-and-swelling/shear-modulus-of-a-swollen-network.md)

## Proof depends on

None.

## Expansion

The first formula follows from the mean-square end-to-end distance $C_\infty n \bar l^2$ of a chain of $n = \lambda N_j$ bonds, a phantom reduction factor $1 - 2/f$, and affine scaling of lengths; each step needs a page. The modulus estimate assumes one elastic chain per sphere of diameter $r_{mesh}$ and $G = \nu k_BT$ ($\pi r_{mesh}^3/6 = k_BT/G$); a radius convention would replace $6/\pi$ by $3/(4\pi)$. Conditions under which the two lengths agree remain to be written.

## Sources

- N. R. Richbourg, A. Ravikumar and N. A. Peppas, "Solute Transport Dependence on 3D Geometry of Hydrogel Networks", Macromolecular Chemistry and Physics (2021), <https://doi.org/10.1002/macp.202100138>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC8389770/>: Eq. (2) and the definitions following it
- Hydrogel Design, "Mesh Transport" (model pages, accessed November 2026), <https://hydrogeldesign.org/the-model/mesh-transport/>: the mesh size equation and the parameter notes (PEG and PVA values, typical ranges)
- T. Canal and N. A. Peppas, "Correlation between mesh size and equilibrium degree of swelling of polymeric networks", Journal of Biomedical Materials Research 23, 1183–1193 (1989), <https://doi.org/10.1002/jbm.820231007>; only the abstract was read, at <https://pubmed.ncbi.nlm.nih.gov/2808463/>: abstract: the correlation between mesh size and equilibrium polymer volume fraction and the change of exponent with water content
- J. Li and D. J. Mooney, "Designing hydrogels for controlled drug delivery", Nature Reviews Materials 1, 16071 (2016), <https://doi.org/10.1038/natrevmats.2016.71>; author manuscript read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC5898614/>: Box 1 (modulus-based mesh length) and the section "Mesh size controls diffusion and release" (typical mesh sizes and protein sizes)
