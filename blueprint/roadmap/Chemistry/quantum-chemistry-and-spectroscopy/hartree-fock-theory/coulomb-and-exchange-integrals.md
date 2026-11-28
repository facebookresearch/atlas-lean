# Coulomb and exchange integrals

The Coulomb integral of two spin-orbitals is the electrostatic repulsion of their charge densities; the exchange integral is the corresponding term in which the two electrons have exchanged orbitals.

For spin-orbitals $\varphi_i,\varphi_j$ (with $x=(r,s)$ and $\int dx$ including the spin sum) for which the integrals are finite, define

$$
J_{ij}=\int\!\!\int\frac{|\varphi_i(x_1)|^2\,|\varphi_j(x_2)|^2}{|r_1-r_2|}\,dx_1dx_2,\qquad K_{ij}=\int\!\!\int\frac{\overline{\varphi_i(x_1)}\,\varphi_j(x_1)\,\overline{\varphi_j(x_2)}\,\varphi_i(x_2)}{|r_1-r_2|}\,dx_1dx_2 .
$$

In the notation $g_{pqrs}=\langle\varphi_p\varphi_q|\varphi_r\varphi_s\rangle$ of the two-electron Slater–Condon rules, $J_{ij}=g_{ijij}$ and $K_{ij}=g_{ijji}$. Immediate properties: $J_{ij}=J_{ji}\ge0$, $K_{ij}=K_{ji}$ is real, $J_{ii}=K_{ii}$, and $K_{ij}=0$ when $\varphi_i$ and $\varphi_j$ are pure-spin orbitals of opposite spin. The associated Coulomb and exchange operators act by $(\hat J_jf)(x)=\int|\varphi_j(x')|^2|r-r'|^{-1}dx'\,f(x)$ and $(\hat K_jf)(x)=\int\overline{\varphi_j(x')}f(x')|r-r'|^{-1}dx'\,\varphi_j(x)$.

## Context

Undergraduate. These integrals make up the Hartree–Fock energy and the Fock operator; the exchange integral between the frontier orbitals controls the singlet–triplet splitting used in screening for inverted-gap emitters.

## Depends on

- [Slater–Condon rules for two-electron operators](../slater-determinants-and-second-quantization/slater-condon-rules-two-electron.md)

## Proof depends on

None.

## Expansion

A definition. $J_{ii}=K_{ii}$ by substitution; the spin statement holds because the integrand of $K_{ij}$ contains $\overline{\varphi_i(x_1)}\varphi_j(x_1)$, which vanishes pointwise in $s_1$ for orbitals of opposite pure spin. $K_{ij}$ is real because swapping $x_1\leftrightarrow x_2$ conjugates the integrand.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.C, Eq. (32) (Coulomb and exchange operators, pp. 22–25). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Jack Simons and Jeff Nichols, *Quantum Mechanics in Chemistry* (Oxford University Press, 1997), open edition on LibreTexts, §18.7 (total energy in terms of $J_{i,j}$ and $K_{i,j}$). [LibreTexts §18.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Book%3A_Quantum_Mechanics__in_Chemistry_(Simons_and_Nichols)/18%3A_Multiconfiguration_Wavefunctions/18.07%3A_Observations_on_Orbitals_and_Orbital_Energies)
