# Fermionic creation and annihilation operators

Creation and annihilation operators add or remove an electron in a given mode of a finite fermionic Fock space, with the sign that keeps occupied modes in increasing order.

Fix $M\ge1$ ordered modes. The fermionic Fock space $\mathcal F_M$ is the $2^M$-dimensional complex Hilbert space with orthonormal basis $|n_1\cdots n_M\rangle$, $n_j\in\{0,1\}$. For $j\in\{1,\dots,M\}$ define linear maps by

$$
a_j^\dagger|n\rangle=\begin{cases}(-1)^{\sum_{l<j}n_l}\,|n_1\cdots 1_j\cdots n_M\rangle,& n_j=0,\\ 0,& n_j=1,\end{cases}\qquad a_j|n\rangle=\begin{cases}(-1)^{\sum_{l<j}n_l}\,|n_1\cdots 0_j\cdots n_M\rangle,& n_j=1,\\ 0,& n_j=0.\end{cases}
$$

Then $a_j$ is the adjoint of $a_j^\dagger$, $\hat n_j=a_j^\dagger a_j$ has $\hat n_j|n\rangle=n_j|n\rangle$, and $\hat N=\sum_j\hat n_j$. For occupied set $j_1<\dots<j_m$, $|n\rangle=a_{j_1}^\dagger\cdots a_{j_m}^\dagger|0\cdots0\rangle$ (the vacuum is the empty product).

**Determinant picture.** If the modes are ordered orthonormal spin-orbitals $\varphi_1,\dots,\varphi_M$, the linear map sending $|n\rangle$ to the Slater determinant of $\varphi_{j_1},\dots,\varphi_{j_m}$ (rows in increasing order), and the vacuum to the number $1$, is an isometry of each $m$-particle sector onto the span of these determinants. The descending product $(a_M^\dagger)^{n_M}\cdots(a_1^\dagger)^{n_1}|0\rangle$ used in some sources equals $(-1)^{m(m-1)/2}|n\rangle$ on an $m$-occupied state; already two occupied modes give a minus sign.

## Context

Undergraduate/graduate. Second quantization is the language of quantum algorithms for chemistry, where occupation states are mapped to qubit basis states; the operators themselves are the canonical finite-mode fermionic algebra, independent of chemistry.

## Depends on

- [Slater determinant](../../../Chemistry/quantum-chemistry-and-spectroscopy/slater-determinants-and-second-quantization/slater-determinant.md)

## Proof depends on

None.

## Expansion

Adjointness: the two maps have the same nonzero matrix entries between basis states, with the same sign. The increasing product reproduces the sign because creating $j_k$ after $j_{k+1},\dots,j_m$ sees no occupied lower mode. Isometry: distinct occupation sets give orthogonal determinants and each is normalized, by the overlap formula of the determinant page. Reversing a product of $m$ distinct anticommuting creation operators takes $m(m-1)/2$ transpositions.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §V.A (pp. 27–28). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix B.1 (occupation states $(a_K^\dagger)^{i_N}\cdots(a_1^\dagger)^{i_1}|vac\rangle$ after Eq. (93)). <https://arxiv.org/abs/1812.09976v2>
