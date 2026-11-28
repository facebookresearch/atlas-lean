# Brillouin's theorem

For a Slater determinant whose orbitals satisfy the Hartree–Fock equations, the energy form vanishes between it and every singly excited determinant.

Fix nuclei and an orthonormal admissible family $\varphi_1,\dots,\varphi_N$ with finite pair integrals and determinant $\Phi$ satisfying the weak Hartree–Fock equations: $f(\chi,\varphi_i)=\sum_j\varepsilon_{ji}\langle\chi,\varphi_j\rangle$ for all $\chi\in\mathcal D$. Let $\varphi_a\in\mathcal D$ be normalized and orthogonal to every $\varphi_j$, and let $\Phi_i^a$ be the determinant with $\varphi_i$ replaced by $\varphi_a$ in the same row. Then

$$
\mathcal E_R(\Phi_i^a,\Phi)=f(\varphi_a,\varphi_i)=0 .
$$

The same holds with $\varphi_a$ restricted to a finite trial space, provided the Hartree–Fock condition holds for $\chi$ in that space. Only this implication is stated; the converse (vanishing for all single excitations implies the Hartree–Fock equations) is the content of the stationarity computation behind the Hartree–Fock equations.

## Context

Undergraduate/graduate. It explains why single excitations do not couple to the Hartree–Fock reference in configuration interaction and why second-order perturbation theory starts with double excitations.

## Depends on

- [Hartree–Fock equations](hartree-fock-equations.md)
- [Fock operator](fock-operator.md)

## Proof depends on

- [Energy form of Slater determinants](../slater-determinants-and-second-quantization/energy-form-of-slater-determinants.md)

## Expansion

The single-replacement case of the energy-form lemma gives $\mathcal E_R(\Phi_i^a,\Phi)=h_{ai}+\sum_j(g_{ajij}-g_{ajji})=f(\varphi_a,\varphi_i)$, and the Hartree–Fock condition with $\chi=\varphi_a$ gives $\sum_j\varepsilon_{ji}\langle\varphi_a,\varphi_j\rangle=0$ by orthogonality.

## Sources

- Jack Simons and Jeff Nichols, *Quantum Mechanics in Chemistry* (Oxford University Press, 1997), open edition on LibreTexts, §18.7, 'The Brillouin Theorem'. [LibreTexts §18.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Book%3A_Quantum_Mechanics__in_Chemistry_(Simons_and_Nichols)/18%3A_Multiconfiguration_Wavefunctions/18.07%3A_Observations_on_Orbitals_and_Orbital_Energies)
- Wim Klopper and David P. Tew, *Second quantization*, lecture notes, C4 Tutorial, Zürich (2006), section 'Brillouin's theorem'. [ipc.kit.edu/theochem/download/Kapitel2.pdf](https://www.ipc.kit.edu/theochem/download/Kapitel2.pdf)
