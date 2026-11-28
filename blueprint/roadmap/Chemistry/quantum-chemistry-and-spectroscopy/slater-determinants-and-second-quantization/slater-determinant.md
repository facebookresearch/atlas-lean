# Slater determinant

A Slater determinant is the antisymmetrized product of $N$ one-electron spin-orbitals with the combinatorial prefactor $1/\sqrt{N!}$; it is normalized exactly when the Gram determinant of its orbitals equals one, for example when they are orthonormal.

Let $x=(r,s)\in\mathbb R^3\times\{\uparrow,\downarrow\}$, with $\int dx$ meaning integration over $r$ and summation over $s$, and let $\varphi_1,\dots,\varphi_N\in L^2(\mathbb R^3\times\{\uparrow,\downarrow\})$, $N\ge1$. The Slater determinant built from them is the $L^2$ class of

$$
\Phi(x_1,\dots,x_N)=\frac{1}{\sqrt{N!}}\det\bigl[\varphi_i(x_j)\bigr]_{i,j=1}^{N}=\sqrt{N!}\,\mathcal A\bigl(\varphi_1(x_1)\cdots\varphi_N(x_N)\bigr),\qquad \mathcal A=\frac{1}{N!}\sum_{\sigma\in S_N}\operatorname{sgn}(\sigma)P_\sigma,
$$

where $P_\sigma$ permutes the electron coordinates and all equalities hold almost everywhere. Properties: $\Phi$ is antisymmetric under exchange of any two coordinates; $\mathcal A$ is an orthogonal projection on $L^2((\mathbb R^3\times\{\uparrow,\downarrow\})^N)$; and

$$
\langle\Phi_\varphi,\Phi_\chi\rangle=\det\bigl[\langle\varphi_i,\chi_j\rangle\bigr]_{i,j=1}^{N},
$$

so $\|\Phi\|^2$ is the Gram determinant of the orbitals, $\Phi=0$ if and only if the orbitals are linearly dependent, and $\|\Phi\|=1$ if and only if that Gram determinant is $1$; orthonormality is sufficient but not necessary (for orthonormal $e_1,e_2$ the pair $2e_1,\frac12e_2$ has Gram determinant $1$). Without orthonormality the prefactor does not normalize: for $N=1$ and $\varphi_1=2u$ with $\|u\|=1$, $\|\Phi\|=2$.

## Context

Undergraduate. The Hartree–Fock reference, the configuration-interaction basis and the computational basis states of fermion-to-qubit encodings are Slater determinants. For real finite-dimensional spaces the overlap formula is the Gram-determinant inner product on exterior powers in Mathlib (`exteriorPower.inner_ιMulti_ιMulti`, with the transposed matrix convention), recorded as a counterpart only.

## Depends on

None.

## Proof depends on

None.

## Expansion

Antisymmetry is the alternating property of the determinant. Each $P_\sigma$ is unitary (Fubini, measure-preserving permutation of coordinates), so $\mathcal A$ is Hermitian, and $\mathcal A^2=\mathcal A$ by reindexing the double sum over the group. For the overlap, move $\mathcal A$ to one side: $\langle\Phi_\varphi,\Phi_\chi\rangle=N!\langle\prod_i\varphi_i(x_i),\mathcal A\prod_i\chi_i(x_i)\rangle=\sum_\sigma\operatorname{sgn}\sigma\prod_i\langle\varphi_i,\chi_{\sigma(i)}\rangle$, the Leibniz expansion of the Gram determinant.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §II.B (pp. 10–12) and §IV.A, Eqs. (20)–(21) (pp. 19–21). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix A (spin-orbitals) and Appendix B (determinant basis). <https://arxiv.org/abs/1812.09976v2>
