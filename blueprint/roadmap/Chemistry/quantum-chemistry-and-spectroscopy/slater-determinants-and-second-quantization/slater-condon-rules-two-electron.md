# Slater–Condon rules for two-electron operators

For the electron-repulsion operator, matrix elements between Slater determinants of orthonormal spin-orbitals reduce to two-electron integrals; determinants differing in three or more orbitals give zero.

Let $\{\varphi_p\}_{p\in P}$ be a finite orthonormal family of spin-orbitals in $L^2(\mathbb R^3\times\{\uparrow,\downarrow\})$ whose pair integrals $\iint|\varphi_p(x_1)|^2|\varphi_q(x_2)|^2|r_1-r_2|^{-1}dx_1dx_2$ are finite for all $p,q\in P$ (including $p=q$). Put

$$
g_{pqrs}=\iint\frac{\overline{\varphi_p(x_1)}\,\overline{\varphi_q(x_2)}\,\varphi_r(x_1)\varphi_s(x_2)}{|r_1-r_2|}\,dx_1\,dx_2 ,
$$

an absolutely convergent integral (physicists' ordering; in Mulliken notation $g_{pqrs}=(pr|qs)$). Let $\hat G=\sum_{1\le i<j\le N}|r_i-r_j|^{-1}$, a multiplication operator, and for determinants $\Phi,\Phi'$ of members of the family let $\langle\Phi,\hat G\Phi'\rangle=\int\overline\Phi\,\hat G\,\Phi'$, which converges absolutely. Let $\Phi$ be the determinant of $\varphi_1,\dots,\varphi_N$ ($N\ge2$); let $\Phi'$ replace $\varphi_i$ by $\varphi_k$, $\Phi''$ replace $\varphi_i,\varphi_j$ ($i\ne j$) by $\varphi_k,\varphi_l$, each in the same row, with $k\ne l$ members not among $\varphi_1,\dots,\varphi_N$. Then

$$
\langle\Phi,\hat G\Phi\rangle=\sum_{1\le i<j\le N}\bigl(g_{ijij}-g_{ijji}\bigr),\qquad \langle\Phi,\hat G\Phi'\rangle=\sum_{j=1}^{N}\bigl(g_{ijkj}-g_{ijjk}\bigr),\qquad \langle\Phi,\hat G\Phi''\rangle=g_{ijkl}-g_{ijlk},
$$

and $\langle\Phi,\hat G\Psi\rangle=0$ for every determinant $\Psi$ of members whose orbital set differs from that of $\Phi$ in three or more orbitals.

## Context

Undergraduate/graduate. The terms $g_{ijij}$ and $g_{ijji}$ are the Coulomb and exchange integrals; the antisymmetrized combinations $g_{ijkl}-g_{ijlk}$ enter second-order perturbation theory. The second-quantized Hamiltonian uses $h_{pqrs}=g_{pqsr}$.

## Depends on

- [Slater determinant](slater-determinant.md)
- [Clamped-nuclei electronic Hamiltonian](../molecular-hamiltonian-and-born-oppenheimer/clamped-nuclei-electronic-hamiltonian.md)

## Proof depends on

None.

## Expansion

Absolute convergence: $|\overline{\varphi_p(x_1)}\varphi_r(x_1)\overline{\varphi_q(x_2)}\varphi_s(x_2)|\le\frac12\bigl(|\varphi_p(x_1)|^2|\varphi_q(x_2)|^2+|\varphi_r(x_1)|^2|\varphi_s(x_2)|^2\bigr)$, and expanding both determinants turns $\overline\Phi\hat G\Phi'$ into finitely many such products. $\hat G$ is permutation symmetric, so the antisymmetrizer moves to one side; for a pair term only the identity and the transposition of the two electrons acted on survive orthonormality, giving direct minus exchange. The $j=i$ term of the single-replacement sum vanishes. If three or more orbitals differ, every term contains an overlap of a member with an orthogonal one in an electron not acted on.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.B, Eqs. (24) and (28)–(31) (pp. 21–22). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
