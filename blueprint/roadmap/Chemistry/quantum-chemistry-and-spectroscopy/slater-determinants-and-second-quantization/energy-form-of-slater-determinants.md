# Energy form of Slater determinants

Slater determinants of an orthonormal family of admissible spin-orbitals with finite pair integrals are admissible electronic states, and their energy-form matrix elements are given by the Slater–Condon rules with the one-electron form in place of the one-electron operator.

Fix nuclei and let $\{\varphi_p\}_{p\in P}$ be a finite orthonormal family of admissible spin-orbitals (elements of $\mathcal A_1(R)$) whose pair integrals $\iint|\varphi_p(x_1)|^2|\varphi_q(x_2)|^2|r_1-r_2|^{-1}dx_1dx_2$ are finite for all $p,q\in P$. Put $h_{pq}=h(\varphi_p,\varphi_q)$ (one-electron form) and $g_{pqrs}$ the two-electron integrals. Then:

1. every Slater determinant $\Phi$ of $N\ge1$ distinct members lies in $\mathcal A_N(R)$;
2. for determinants $\Phi,\Psi$ of members, $\mathcal E_R(\Phi,\Psi)$ equals the sum of the one-electron Slater–Condon expression with $h_{pq}$ and the two-electron Slater–Condon expression with $g_{pqrs}$. In particular

$$
E_R(\Phi)=\sum_{i=1}^{N}h_{ii}+\sum_{1\le i<j\le N}\bigl(g_{ijij}-g_{ijji}\bigr),
$$

the single-replacement element is $h_{ik}+\sum_j(g_{ijkj}-g_{ijjk})$, the double-replacement element is $g_{ijkl}-g_{ijlk}$, and determinants differing in three or more orbitals give $0$ (same-row replacement convention).

## Context

Undergraduate/graduate. This is the bridge between the continuum energy form and the finite matrix problems of Hartree–Fock theory, configuration interaction and quantum algorithms.

## Depends on

- [Slater determinant](slater-determinant.md)
- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)

## Proof depends on

- [Slater–Condon rules for one-electron operators](slater-condon-rules-one-electron.md)
- [Slater–Condon rules for two-electron operators](slater-condon-rules-two-electron.md)

## Expansion

(1) Each term $\prod_j\varphi_{\sigma(j)}(x_j)$ of the determinant has real and imaginary parts of its spin components in $H^1(\mathbb R^{3N})$ with $\nabla_{r_i}$ acting on the $i$-th factor only (weak derivative of a product of functions of separate variables, by Fubini); antisymmetry holds by the determinant page. Coulomb integrability: $|\Phi|^2\le\sum_\sigma\prod_j|\varphi_{\sigma(j)}(x_j)|^2$ by Cauchy–Schwarz over the $N!$ terms, and integrating against $|r_i-R_A|^{-1}$ or $|r_i-r_j|^{-1}$ gives finite sums of one-orbital attraction integrals or pair integrals times norms. (2) The kinetic-plus-attraction part of $\mathcal E_R$ is a sum over electrons of one-body forms, symmetric under permutations; the antisymmetrizer computation of the one-electron rules applies verbatim with $h_{pq}$ the one-electron form, and the repulsion part is the two-electron rule. Missing prerequisite on the graph: the weak-derivative rule for products of Sobolev functions of separate variables (tensor products in $H^1$).

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.B, Eqs. (22)–(31) (pp. 21–22). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Mathieu Lewin, Elliott H. Lieb and Robert Seiringer, *Universal Functionals in Density Functional Theory*, chapter in *Density Functional Theory — Modeling, Mathematical Analysis, Computational Methods, and Applications*; numbers from arXiv:1912.10424v4, §1, Eq. (3) (energy space). <https://arxiv.org/abs/1912.10424v4>
