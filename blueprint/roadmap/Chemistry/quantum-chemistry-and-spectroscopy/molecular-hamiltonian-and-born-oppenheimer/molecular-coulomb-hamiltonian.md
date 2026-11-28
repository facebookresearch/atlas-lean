# Molecular Coulomb Hamiltonian

The molecular Coulomb Hamiltonian is the nonrelativistic energy operator of $N$ electrons and $M$ point nuclei interacting only through Coulomb forces, written in atomic units.

Fix $N\ge1$ electrons with positions $r_1,\dots,r_N\in\mathbb R^3$ and spins $s_i\in\{\uparrow,\downarrow\}$, and $M\ge1$ nuclei with positions $R_1,\dots,R_M\in\mathbb R^3$, charges $Z_A\in\mathbb Z_{>0}$ and masses $M_A>0$ measured in electron masses. In atomic units ($\hbar=m_e=e=4\pi\varepsilon_0=1$) the molecular Hamiltonian is the differential expression

$$
\hat H_{\mathrm{mol}}=-\sum_{A=1}^{M}\frac{\nabla_{R_A}^2}{2M_A}-\sum_{i=1}^{N}\frac{\nabla_{r_i}^2}{2}-\sum_{i=1}^{N}\sum_{A=1}^{M}\frac{Z_A}{|r_i-R_A|}+\sum_{1\le i<j\le N}\frac{1}{|r_i-r_j|}+\sum_{1\le A<B\le M}\frac{Z_AZ_B}{|R_A-R_B|}.
$$

It acts on wave functions $\Psi(R_1,\dots,R_M;x_1,\dots,x_N)$ with $x_i=(r_i,s_i)$ that are antisymmetric under every simultaneous exchange $x_i\leftrightarrow x_j$ of two electrons' positions and spins. The Coulomb terms are singular on the coincidence sets $r_i=r_j$, $r_i=R_A$ and $R_A=R_B$, which have Lebesgue measure zero. The time-independent Schrödinger equation is $\hat H_{\mathrm{mol}}\Psi=E\Psi$.

Conventions: the nuclear permutation symmetry and nuclear spins are not imposed; the page fixes only the differential expression, not a self-adjoint realization or its domain.

## Context

Undergraduate. The starting point of molecular electronic-structure theory; the review of Cao, Aspuru-Guzik and coauthors opens its treatment of classical quantum chemistry with this Hamiltonian and its Born–Oppenheimer splitting.

## Depends on

None.

## Proof depends on

None.

## Expansion

A definition. The atomic-unit form follows from the SI Hamiltonian by measuring lengths in Bohr radii, energies in hartree and masses in electron masses. A rigorous treatment would add the quadratic-form realization on the antisymmetric Sobolev space $H^1$.

## Sources

- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.1, Eqs. (1) and (3). <https://arxiv.org/abs/1812.09976v2>
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §III.A (pp. 13–15). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
