# Clamped-nuclei electronic Hamiltonian

The clamped-nuclei (electronic) Hamiltonian is the part of the molecular Hamiltonian that acts on the electrons when the nuclei are held fixed at given positions.

Fix pairwise distinct nuclear positions $R=(R_1,\dots,R_M)$ with charges $Z_A\in\mathbb Z_{>0}$, and $N\ge1$ electrons with coordinates $x_i=(r_i,s_i)\in\mathbb R^3\times\{\uparrow,\downarrow\}$. In atomic units the electronic Hamiltonian is

$$
\hat H_{\mathrm{el}}(R)=-\frac12\sum_{i=1}^{N}\nabla_{r_i}^2-\sum_{i=1}^{N}\sum_{A=1}^{M}\frac{Z_A}{|r_i-R_A|}+\sum_{1\le i<j\le N}\frac{1}{|r_i-r_j|},
$$

acting on wave functions antisymmetric under simultaneous exchange of electron positions and spins. The nuclear positions enter only as parameters. The nuclear repulsion

$$
V_{NN}(R)=\sum_{1\le A<B\le M}\frac{Z_AZ_B}{|R_A-R_B|}
$$

is a constant for fixed $R$; adding it gives $\hat H_{\mathrm{el}}(R)+V_{NN}(R)$, the form written in some sources.

## Context

Undergraduate. This is the Hamiltonian whose ground-state energy quantum-chemistry methods approximate, classical and quantum alike; the review of Cao, Aspuru-Guzik and coauthors calls it "the Hamiltonian of interest to quantum chemistry".

## Depends on

- [Molecular Coulomb Hamiltonian](molecular-coulomb-hamiltonian.md)

## Proof depends on

None.

## Expansion

Obtained from the molecular Coulomb Hamiltonian by deleting the nuclear kinetic energy, which formally corresponds to infinite nuclear masses. Whether $V_{NN}$ is included is a convention: Eq. (6) of the review omits it and Eq. (100) includes it.

## Sources

- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.1, Eq. (6), and Appendix C.2, Eq. (100). <https://arxiv.org/abs/1812.09976v2>
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §III.B (p. 15). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
