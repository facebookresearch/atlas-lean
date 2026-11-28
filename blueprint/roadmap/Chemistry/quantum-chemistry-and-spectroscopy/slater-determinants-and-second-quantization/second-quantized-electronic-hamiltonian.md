# Second-quantized electronic Hamiltonian

In a finite orthonormal basis of admissible spin-orbitals, the electronic Hamiltonian is represented on Fock space by Hermitian one- and two-electron integral tensors multiplying products of creation and annihilation operators.

Fix nuclei and a finite orthonormal family $\varphi_1,\dots,\varphi_M$ of admissible spin-orbitals with finite pair integrals. Define, with $\int dx$ summing over spin,

$$
h_{pq}=h(\varphi_p,\varphi_q)=\int\Bigl(\frac12\overline{\nabla\varphi_p}\cdot\nabla\varphi_q-\sum_{A}\frac{Z_A}{|r-R_A|}\overline{\varphi_p}\varphi_q\Bigr)dx,\qquad h_{pqrs}=\iint\frac{\overline{\varphi_p(x_1)}\,\overline{\varphi_q(x_2)}\,\varphi_s(x_1)\varphi_r(x_2)}{|r_1-r_2|}\,dx_1dx_2 ,
$$

the one-electron form and the two-electron integrals (so $h_{pqrs}=g_{pqsr}$ in Slater–Condon notation), both absolutely convergent. On $\mathcal F_M$ put

$$
\hat H=\sum_{p,q=1}^{M}h_{pq}\,a_p^\dagger a_q+\frac12\sum_{p,q,r,s=1}^{M}h_{pqrs}\,a_p^\dagger a_q^\dagger a_r a_s .
$$

Then $h_{pq}=\overline{h_{qp}}$ and $h_{pqrs}=\overline{h_{srqp}}=h_{qpsr}$, so $\hat H$ is Hermitian, and $\hat H$ commutes with the number operator. If the nuclear repulsion is included it is added as $V_{NN}\mathbf 1$ on every particle-number sector.

## Context

Undergraduate/graduate. With integrals precomputed classically, this operator is the input to the qubit Hamiltonians of variational and phase-estimation algorithms; it has $O(M^4)$ terms. When the ket $\varphi_q$ is a Schwartz function, $h_{pq}=\langle\varphi_p,(-\frac12\nabla^2+v)\varphi_q\rangle$ by integration by parts, the operator form printed in the sources; for a general admissible $\varphi_q$ the Laplacian is only a distribution and the form is the definition.

## Depends on

- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)
- [Fermionic creation and annihilation operators](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/fermionic-creation-and-annihilation-operators.md)
- [Slater–Condon rules for two-electron operators](slater-condon-rules-two-electron.md)

## Proof depends on

- [Canonical anticommutation relations](../../../Physics/quantum-mechanics/finite-fermionic-fock-space/canonical-anticommutation-relations.md)

## Expansion

$h_{pq}=\overline{h_{qp}}$ because the one-electron form is Hermitian. For $h_{pqrs}$, complex conjugation gives $\overline{h_{srqp}}$ and relabelling $x_1\leftrightarrow x_2$ gives $h_{qpsr}$; the adjoint of $a_p^\dagger a_q^\dagger a_ra_s$ is $a_s^\dagger a_r^\dagger a_qa_p$, so $\hat H^\dagger=\hat H$. Each term has equally many creation and annihilation operators, hence commutes with $\hat N$ by the anticommutation relations. Two corrections to the review of Cao, Aspuru-Guzik and coauthors: its Eq. (102) prints the kinetic term with $+\nabla^2/2$ (Eqs. (6) and (100) of the same source, and Eq. (3) of Whitfield, Biamonte and Aspuru-Guzik, have $-\nabla^2/2$), and its §2.3 Eq. (8) is an energy quotient, not this operator.

## Sources

- James D. Whitfield, Jacob Biamonte and Alán Aspuru-Guzik, *Simulation of electronic structure Hamiltonians using quantum computers*, Mol. Phys. 109 (2011) 735–750, <https://doi.org/10.1080/00268976.2011.552441>; numbers from the author manuscript in Harvard DASH, §3, Eqs. (1), (3) and (4). [dash.harvard.edu author manuscript](https://dash.harvard.edu/server/api/core/bitstreams/7312037c-8dbe-6bd4-e053-0100007fdf3b/content)
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix C.2, Eqs. (101)–(103). <https://arxiv.org/abs/1812.09976v2>
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §V.C (pp. 30–31). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
