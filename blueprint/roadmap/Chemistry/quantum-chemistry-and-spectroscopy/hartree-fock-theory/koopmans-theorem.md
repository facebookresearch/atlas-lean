# Koopmans' theorem

In the frozen-orbital single-determinant model, removing an electron from a canonical Hartree–Fock spin-orbital changes the energy by minus its orbital energy, and adding one to a canonical virtual spin-orbital changes it by plus its orbital energy.

Fix nuclei and canonical Hartree–Fock orbitals $\varphi_1,\dots,\varphi_N$ (orthonormal, admissible, finite pair integrals) with orbital energies $\varepsilon_i$, Fock form $f$ on $\mathcal D$, and $E_N=E_R(\Phi)$ the energy of their determinant; all energies use the same nuclei and the electronic energy form without $V_{NN}$. (a) If $N\ge2$ and $1\le k\le N$, let $E_{N-1}^{(k)}$ be the energy of the determinant of the occupied orbitals with $\varphi_k$ removed; then $E_{N-1}^{(k)}-E_N=-\varepsilon_k$. (b) If $\varphi_a\in\mathcal D$ is normalized, orthogonal to every $\varphi_i$, and a weak eigenfunction of the same Fock form with energy $\varepsilon_a$, let $E_{N+1}^{(a)}$ be the energy of the determinant with $\varphi_a$ added; then $E_{N+1}^{(a)}-E_N=\varepsilon_a$.

These are the Koopmans estimates $-\varepsilon_k$ of a vertical ionization energy and $-\varepsilon_a$ of a vertical electron affinity; they neglect orbital relaxation and correlation and are not the exact quantities.

## Context

Undergraduate. A standard qualitative tool (errors of a few tenths of an electronvolt are typical, according to the textbook source). With the convention that the empty determinant has energy $0$, part (a) also holds for $N=1$, where $E_1=h_{11}=\varepsilon_1$. In a finite basis, part (b) is instantiated only when a virtual orbital exists.

## Depends on

- [Fock operator](fock-operator.md)
- [Energy of a Slater determinant](hartree-fock-energy-of-a-determinant.md)

## Proof depends on

- [Coulomb and exchange integrals](coulomb-and-exchange-integrals.md)

## Expansion

Subtract the two energy expressions: all terms not involving the removed (added) orbital cancel, leaving $h_{kk}+\sum_{j\le N}(J_{kj}-K_{kj})=f(\varphi_k,\varphi_k)=\varepsilon_k$, where the term $j=k$ vanishes because $J_{kk}=K_{kk}$; for addition the remainder is $h_{aa}+\sum_{j\le N}(J_{aj}-K_{aj})=f(\varphi_a,\varphi_a)=\varepsilon_a$.

## Sources

- Jack Simons and Jeff Nichols, *Quantum Mechanics in Chemistry* (Oxford University Press, 1997), open edition on LibreTexts, §18.7, 'Koopmans' Theorem'. [LibreTexts §18.7](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Book%3A_Quantum_Mechanics__in_Chemistry_(Simons_and_Nichols)/18%3A_Multiconfiguration_Wavefunctions/18.07%3A_Observations_on_Orbitals_and_Orbital_Energies)
- Jack Simons, *Advanced Theoretical Chemistry*, open textbook on LibreTexts, §6.3 'The Hartree-Fock Approximation' (Koopmans' theorem). [LibreTexts §6.3](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Advanced_Theoretical_Chemistry_(Simons)/06:_Electronic_Structure/6.03:_The_Hartree-Fock_Approximation)
