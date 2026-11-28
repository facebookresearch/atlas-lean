# Born–Oppenheimer potential energy surface

The Born–Oppenheimer potential energy surface assigns to each nuclear configuration the electronic ground-state energy plus the nuclear repulsion; in the Born–Oppenheimer model it is the potential in which the nuclei move.

For pairwise distinct nuclear positions $R=(R_1,\dots,R_M)$ the surface is

$$
U(R)=E_{\mathrm{el}}(R)+V_{NN}(R)\in[-\infty,\infty),
$$

where $E_{\mathrm{el}}(R)$ is the infimum of the electronic energy form over normalized admissible $N$-electron states and $V_{NN}(R)=\sum_{A<B}Z_AZ_B|R_A-R_B|^{-1}$. The infimum need not be attained: for a negative ion with too many electrons there may be no normalizable ground state, and nothing about $R$ or the mass ratio supplies one.

**Born–Oppenheimer model.** Suppose that on an open set $\Omega$ of configurations a normalized admissible eigenfunction $\chi_R$ of the electronic problem with eigenvalue $E_{\mathrm{el}}(R)$ is chosen, depending smoothly on $R$. The model replaces the molecular eigenvalue problem by the product ansatz $\Psi(R,x)\approx\varphi(R)\chi_R(x)$ and the nuclear equation

$$
\Bigl(-\sum_{A=1}^{M}\frac{\nabla_{R_A}^2}{2M_A}+U(R)\Bigr)\varphi(R)=E\,\varphi(R)\qquad(R\in\Omega),
$$

obtained by neglecting the terms in which nuclear derivatives act on $\chi_R$: the first-derivative couplings $\langle\chi_R,\nabla_{R_A}\chi_R\rangle\cdot\nabla_{R_A}\varphi/M_A$ and the second-derivative term $\langle\chi_R,\nabla_{R_A}^2\chi_R\rangle\varphi/(2M_A)$. It is a stipulated approximation, not a consequence of the molecular Hamiltonian.

## Context

Undergraduate (surface) and graduate (model). The hydrogen-molecule dissociation curve in the review of Cao, Aspuru-Guzik and coauthors (Fig. 10) is a finite-basis (STO-6G) full configuration interaction approximation to a section of this surface, not the exact continuum surface.

## Depends on

- [Electronic energy form](electronic-energy-form.md)
- [Clamped-nuclei electronic Hamiltonian](clamped-nuclei-electronic-hamiltonian.md)
- [Molecular Coulomb Hamiltonian](molecular-coulomb-hamiltonian.md)

## Proof depends on

None.

## Expansion

A definition plus a model. Inserting the product ansatz into the molecular Schrödinger equation, taking the inner product with $\chi_R$ in the electronic variables and dropping the two listed coupling terms gives the nuclear equation. Existence and smoothness of an isolated eigenvalue branch, and error estimates in powers of the mass ratio, are separate results (see the survey of Hagedorn and Joye) and are not claimed.

## Sources

- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.1, Eqs. (4), (5) and (7), and Appendix C.2 (Fig. 10). <https://arxiv.org/abs/1812.09976v2>
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §III.B–III.C (pp. 15–17). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
