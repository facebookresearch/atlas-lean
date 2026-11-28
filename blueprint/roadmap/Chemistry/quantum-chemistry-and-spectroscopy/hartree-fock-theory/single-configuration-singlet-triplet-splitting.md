# Singlet–triplet splitting of a single excited configuration

For one electron promoted between two orbitals of a closed-shell configuration, the singlet and triplet states built from the same orbitals differ in energy by twice the exchange integral of the two orbitals, so at this level the singlet is not below the triplet.

Fix nuclei and real admissible spatial orbitals $\psi_1,\dots,\psi_m$, orthonormal, with an occupied index $x\le m$ and a unit real admissible orbital $\psi_y$ orthogonal to every $\psi_j$, all pair integrals finite. Form the $2m$-electron states in which every $\psi_j$ ($j\ne x$) is doubly occupied and one electron each occupies $\psi_x$ and $\psi_y$, and let ${}^1\Psi$ and ${}^3\Psi$ be the normalized singlet ($S=0$) and $M_S=0$ triplet ($S=1$) states of this configuration. For the spin-independent electronic energy form,

$$
E_R({}^1\Psi)-E_R({}^3\Psi)=2K_{xy},\qquad K_{xy}=(xy|yx)=\iint\frac{\psi_x(r_1)\psi_y(r_1)\psi_y(r_2)\psi_x(r_2)}{|r_1-r_2|}\,dr_1dr_2 .
$$

If moreover $\psi_x\psi_y\in L^1\cap L^{6/5}(\mathbb R^3)$, then $K_{xy}\ge0$. These are energies of the two shared-orbital configurations, not in general the exact $S_1$ and $T_1$ eigenvalues.

## Context

Graduate/research. Jorner, Pollice, Lavigne and Aspuru-Guzik use this expression to explain why molecules with inverted singlet–triplet gaps, candidate emitters for organic light-emitting diodes, need correlation beyond a single configuration (they attribute the inversion to dynamic spin polarization via doubly excited configurations), and screen for them with a Pariser–Parr–Pople model plus perturbation theory; the screening results are computational evidence, not part of this statement.

## Depends on

- [Coulomb and exchange integrals](coulomb-and-exchange-integrals.md)
- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)

## Proof depends on

- [Energy form of Slater determinants](../slater-determinants-and-second-quantization/energy-form-of-slater-determinants.md)
- [Positive semidefiniteness of the two-electron integral matrix](two-electron-integrals-positive-semidefinite.md)

## Expansion

The two states share the closed-shell core and differ only in the two active electrons. The singlet carries the symmetric spatial function $(\psi_x(r_1)\psi_y(r_2)+\psi_y(r_1)\psi_x(r_2))/\sqrt2$ (with the antisymmetric spin singlet) and the triplet the antisymmetric spatial function (with a symmetric spin triplet); all core and one-electron contributions coincide, and the active-pair repulsion is $J_{xy}+K_{xy}$ for the symmetric and $J_{xy}-K_{xy}$ for the antisymmetric spatial function. Both states are combinations of two determinants, so the energies follow from the energy-form lemma; nonnegativity of $K_{xy}$ is the exchange corollary of the positive semidefiniteness page.

## Sources

- Kjell Jorner, Robert Pollice, Cyrille Lavigne and Alán Aspuru-Guzik, *Ultrafast Computational Screening of Molecules with Inverted Singlet–Triplet Energy Gaps Using the Pariser–Parr–Pople Semiempirical Quantum Chemistry Method*, J. Phys. Chem. A 128 (2024) 2445–2456, <https://doi.org/10.1021/acs.jpca.3c06357> (PMC10983003), Eq. (13) and the surrounding discussion of dynamic spin polarization.
