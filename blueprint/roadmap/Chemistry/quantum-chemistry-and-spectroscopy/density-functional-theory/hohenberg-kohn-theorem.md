# Hohenberg–Kohn theorem

Two many-electron Hamiltonians that differ only in their one-body potentials and have ground states with the same one-particle density have potentials that differ by a constant.

Let $d\ge1$, $N\ge1$, $p>\max(2d/3,2)$, and let $w,v_1,v_2\in(L^p+L^\infty)(\mathbb R^d,\mathbb R)$ with $w$ even ($w(-x)=w(x)$). For such $v$ let $H^N(v)=\sum_{i=1}^{N}(-\Delta_{x_i}+v(x_i))+\sum_{i<j}w(x_i-x_j)$, realized as a self-adjoint operator through its quadratic form, acting either on $L^2(\mathbb R^{dN})$ or on the subspace of functions of $N$ particles with $q$ spin states that are antisymmetric under joint permutations of positions and spins (a reducing subspace because $w$ is even and the potentials are spin independent). For normalized $\Psi$ let $\rho_\Psi(x)=\sum_{s}\sum_{i=1}^{N}\int|\Psi_s(x_1,\dots,x_{i-1},x,x_{i+1},\dots,x_N)|^2\prod_{j\ne i}dx_j$, summed over spin labels. If $\Psi_1,\Psi_2$ are normalized eigenfunctions of $H^N(v_1)$ and $H^N(v_2)$ for the lowest eigenvalues of these operators on the chosen subspace and $\rho_{\Psi_1}=\rho_{\Psi_2}$, then $v_1-v_2$ is almost everywhere equal to a constant. The physical case $d=3$, $w(x)=|x|^{-1}$, $v=-\sum_AZ_A|x-R_A|^{-1}$ is covered. No nondegeneracy assumption is needed.

## Context

Graduate/research. The theorem underlies density-functional theory; Lieb showed that a complete proof needs a strong unique continuation property, which Garrigue established for these $N$-independent assumptions. The kinetic coefficient $1$ instead of $\frac12$ is immaterial; Coulomb potentials fit by taking $2<p<3$ near the singularity and a bounded remainder.

## Depends on

- [Clamped-nuclei electronic Hamiltonian](../molecular-hamiltonian-and-born-oppenheimer/clamped-nuclei-electronic-hamiltonian.md)

## Proof depends on

None.

## Expansion

Using $\Psi_2$ as a trial state for $H^N(v_1)$ gives $E_1\le E_2+\int(v_1-v_2)\rho$, and symmetrically $E_2\le E_1+\int(v_2-v_1)\rho$, since the densities agree; adding shows equality, so $\Psi_2$ minimizes the form of $H^N(v_1)$ and is an eigenfunction of it. Subtracting the two eigenvalue equations gives $\sum_i(v_1-v_2)(x_i)\,\Psi_2=(E_1-E_2)\Psi_2$ almost everywhere, for every spin component. Choose a nonzero spin component; it solves a scalar Schrödinger equation and lies in $H^2_{\mathrm{loc}}$, so by the strong unique continuation property (Garrigue, Corollary 1.2) it vanishes only on a null set. Hence $\sum_i(v_1-v_2)(x_i)=E_1-E_2$ almost everywhere on $\mathbb R^{dN}$, and freezing all but one variable (Fubini) shows $v_1-v_2$ is a.e. constant. Missing prerequisites on the graph: the form realization of $H^N(v)$ with $H^2_{\mathrm{loc}}$ regularity of eigenfunctions, and strong unique continuation for many-body Schrödinger operators. The corollary and theorem displays of arXiv:1804.07564v7 print the exponent condition as $p>\max(2d/3)$; the abstract and proof use $p>\max(2d/3,2)$, as here.

## Sources

- Louis Garrigue, *Unique continuation for many-body Schrödinger operators and the Hohenberg-Kohn theorem*, Math. Phys. Anal. Geom. 21 (2018) 27, Corollary 1.2 and Theorem 1.3 with its proof; arXiv:1804.07564v7. <https://arxiv.org/abs/1804.07564v7>
- Louis Garrigue, *Unique continuation for many-body Schrödinger operators and the Hohenberg-Kohn theorem. II. The Pauli Hamiltonian*, Doc. Math. 25 (2020) 869–898, <https://doi.org/10.4171/dm/765>, footnote 1 and Corollary 2.2 (the Carleman estimate needed by the first paper).
