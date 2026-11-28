# Matrix elements of the second-quantized Hamiltonian

On each sector with $N\ge1$ particles, the second-quantized electronic Hamiltonian has exactly the energy-form matrix elements between the corresponding Slater determinants.

Fix nuclei and a finite orthonormal family $\varphi_1,\dots,\varphi_M$ of admissible spin-orbitals with finite pair integrals, and let $\hat H$ be the second-quantized electronic Hamiltonian built from them (without $V_{NN}$). For $1\le N\le M$ and an occupation vector $n$ with $\sum_jn_j=N$, let $\Phi_n$ be the Slater determinant of the occupied orbitals in increasing order. Then for all such $n,n'$

$$
\langle n|\hat H|n'\rangle=\mathcal E_R(\Phi_n,\Phi_{n'}),
$$

where $\mathcal E_R$ is the electronic energy form. The determinants $\Phi_n$ form an orthonormal basis of their span $V_N$, so the restriction of $\hat H$ to the $N$-particle sector of $\mathcal F_M$ is unitarily equivalent to the matrix of $\mathcal E_R$ on $V_N$ (the finite compression of the form). It identifies only this compression, not an invariant subspace of the continuum problem. If $V_{NN}$ is added, it is added on both sides.

## Context

Undergraduate/graduate. This justifies replacing the electronic problem in a finite basis by a finite matrix problem on qubits.

## Depends on

- [Second-quantized electronic Hamiltonian](second-quantized-electronic-hamiltonian.md)
- [Energy form of Slater determinants](energy-form-of-slater-determinants.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

Orthonormality of the $\Phi_n$: the overlap of two determinants is the determinant of orbital overlaps, which is $1$ for equal occupation sets and has a zero row otherwise. Compute $\langle n|a_p^\dagger a_q|n'\rangle$ and $\langle n|a_p^\dagger a_q^\dagger a_ra_s|n'\rangle$ with the anticommutation relations: they vanish unless $n'$ differs from $n$ in at most one, respectively two, occupied orbitals. In the surviving cases the parity signs from moving operators past occupied lower modes equal the signs from sorting the replaced rows of the determinant into increasing order, and the coefficients reproduce the Slater–Condon expressions with $h_{pq}$ and $g_{pqrs}=h_{pqsr}$ given by the energy-form lemma.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §V.C (pp. 30–31). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix C.2, Eq. (101). <https://arxiv.org/abs/1812.09976v2>
