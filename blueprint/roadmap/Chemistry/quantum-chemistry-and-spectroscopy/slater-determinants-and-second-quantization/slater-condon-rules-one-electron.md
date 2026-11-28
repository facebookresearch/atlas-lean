# Slater–Condon rules for one-electron operators

The Slater–Condon rules express matrix elements of a sum of one-electron operators between Slater determinants of orthonormal spin-orbitals through one-orbital integrals; determinants differing in two or more orbitals give zero.

Let $\{\varphi_p\}$ be an orthonormal set of spin-orbitals, $h$ a Hermitian one-electron operator for which all integrals $h_{pq}=\langle\varphi_p,h\varphi_q\rangle$ below are finite, and $\hat F=\sum_{i=1}^{N}h(i)$, where $h(i)$ acts on electron $i$. Let $\Phi$ be the Slater determinant of $\varphi_1,\dots,\varphi_N$; let $\Phi'$ be obtained by replacing $\varphi_i$ by $\varphi_k$ ($k>N$) in the same row; and let $\Phi''$ be obtained by two such replacements. Then

$$
\langle\Phi,\hat F\Phi\rangle=\sum_{i=1}^{N}h_{ii},\qquad \langle\Phi,\hat F\Phi'\rangle=h_{ik},\qquad \langle\Phi,\hat F\Phi''\rangle=0 .
$$

## Context

Undergraduate/graduate. Together with the two-electron rules these give the Hartree–Fock energy, the configuration-interaction matrix and the second-quantized form of the Hamiltonian.

## Depends on

- [Slater determinant](slater-determinant.md)

## Proof depends on

None.

## Expansion

$\hat F$ is symmetric under permutations of electrons, so it commutes with the antisymmetrizer; moving the idempotent Hermitian antisymmetrizer onto one side leaves a single product function, and orthonormality kills every permuted term except those in which the electron acted on by $h$ carries the replaced orbital. The sign is $+1$ because the replacement keeps the row position.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.B, Eqs. (22)–(27) (pp. 21–22). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Jack Simons and Jeff Nichols, *Quantum Mechanics in Chemistry* (Oxford University Press, 1997), open edition on LibreTexts, §18.7 (Slater–Condon rules used for the total energy). [LibreTexts §18.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Book%3A_Quantum_Mechanics__in_Chemistry_(Simons_and_Nichols)/18%3A_Multiconfiguration_Wavefunctions/18.07%3A_Observations_on_Orbitals_and_Orbital_Energies)
