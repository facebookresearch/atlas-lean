# Energy of a Slater determinant

The electronic energy of a Slater determinant of orthonormal admissible spin-orbitals is the sum of one-electron energies plus the Coulomb-minus-exchange energy of all occupied pairs; for canonical Hartree–Fock orbitals it differs from the sum of orbital energies by that pair energy.

Fix nuclei and an orthonormal family $\varphi_1,\dots,\varphi_N$ ($N\ge1$) of admissible spin-orbitals with finite pair integrals, with Slater determinant $\Phi$, and let $\mathcal D$ be the set of admissible spin-orbitals $\chi$ whose pair integrals with $\chi$ itself and with every $\varphi_j$ are finite. With $h_{ii}=h(\varphi_i,\varphi_i)$ the one-electron form,

$$
E_R(\Phi)=\sum_{i=1}^{N}h_{ii}+\sum_{1\le i<j\le N}\bigl(J_{ij}-K_{ij}\bigr)=\sum_{i=1}^{N}h_{ii}+\frac12\sum_{i,j=1}^{N}\bigl(J_{ij}-K_{ij}\bigr).
$$

If the orbitals are canonical Hartree–Fock orbitals with orbital energies $\varepsilon_i$, then

$$
E_R(\Phi)=\frac12\sum_{i=1}^{N}\bigl(h_{ii}+\varepsilon_i\bigr)=\sum_{i=1}^{N}\varepsilon_i-\sum_{1\le i<j\le N}\bigl(J_{ij}-K_{ij}\bigr).
$$

The two agree exactly when the pair energy vanishes, as for $N=1$. The Hartree–Fock energy is the infimum of $E_R$ over such determinants, in $[-\infty,\infty)$; it need not be attained.

## Context

Undergraduate. Quantum algorithms use the minimizing determinant, when it exists, as their reference state.

## Depends on

- [Slater determinant](../slater-determinants-and-second-quantization/slater-determinant.md)
- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)
- [Coulomb and exchange integrals](coulomb-and-exchange-integrals.md)
- [Fock operator](fock-operator.md)

## Proof depends on

- [Energy form of Slater determinants](../slater-determinants-and-second-quantization/energy-form-of-slater-determinants.md)

## Expansion

The diagonal case of the energy-form lemma gives the first formula, with $g_{ijij}=J_{ij}$ and $g_{ijji}=K_{ij}$; the two sums agree because $J_{ii}=K_{ii}$. For canonical orbitals $\varepsilon_i=f(\varphi_i,\varphi_i)=h_{ii}+\sum_j(J_{ij}-K_{ij})$, and summing over $i$ counts each pair term twice.

## Sources

- Jack Simons and Jeff Nichols, *Quantum Mechanics in Chemistry* (Oxford University Press, 1997), open edition on LibreTexts, §18.7, 'Orbital Energies and the Total Energy'. [LibreTexts §18.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Book%3A_Quantum_Mechanics__in_Chemistry_(Simons_and_Nichols)/18%3A_Multiconfiguration_Wavefunctions/18.07%3A_Observations_on_Orbitals_and_Orbital_Energies)
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.B–IV.C (pp. 21–25). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- C. David Sherrill, *An Introduction to Hartree-Fock Molecular Orbital Theory*, lecture notes, School of Chemistry and Biochemistry, Georgia Institute of Technology (June 2000), §6 (energy expression). [vergil.chemistry.gatech.edu/static/content/hf-intro.pdf](https://vergil.chemistry.gatech.edu/static/content/hf-intro.pdf)
