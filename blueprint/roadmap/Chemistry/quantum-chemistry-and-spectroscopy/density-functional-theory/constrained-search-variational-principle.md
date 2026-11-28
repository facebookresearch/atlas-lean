# Constrained-search variational principle

The infimum of the energy of an electronic Hamiltonian with external potential $v$ equals the infimum over densities of a universal density functional plus the potential energy, where the universal functional is a constrained search over wave functions with the given density.

Let $\mathcal A_N$ be the admissible $N$-electron states of the electronic energy form (antisymmetric, spin components with real and imaginary parts in $H^1$, finite pair Coulomb integrals), and for normalized $\Psi\in\mathcal A_N$ let $\rho_\Psi(r)=\sum_s\sum_{i=1}^{N}\int|\psi_s|^2\prod_{j\ne i}dr_j$ (spin-summed one-particle density, $\int\rho_\Psi=N$). Let $\mathcal D_N=\{\rho_\Psi\}$ and define the Levy–Lieb functional

$$
F_{\mathrm{LL}}[\rho]=\inf\Bigl\{\sum_s\int\Bigl(\frac12\sum_i|\nabla_{r_i}\psi_s|^2+W|\psi_s|^2\Bigr):\ \Psi\in\mathcal A_N,\ \|\Psi\|=1,\ \rho_\Psi=\rho\Bigr\}\qquad(\rho\in\mathcal D_N),
$$

with $W=\sum_{i<j}|r_i-r_j|^{-1}$. Let $v:\mathbb R^3\to\mathbb R$ be measurable, and call a normalized $\Psi\in\mathcal A_N$ $v$-admissible if $\int|v|\rho_\Psi<\infty$. Then

$$
\inf_{\Psi\ v\text{-admissible}}\Bigl(\sum_s\int\Bigl(\frac12\sum_i|\nabla_{r_i}\psi_s|^2+W|\psi_s|^2\Bigr)+\int v\rho_\Psi\Bigr)=\inf\Bigl\{F_{\mathrm{LL}}[\rho]+\int v\rho:\ \rho\in\mathcal D_N,\ \int|v|\rho<\infty\Bigr\},
$$

both sides in $[-\infty,\infty]$. $F_{\mathrm{LL}}$ does not depend on $v$, and no ground state or attainment of any infimum is assumed.

## Context

Graduate. This is the rigorous replacement of the second Hohenberg–Kohn theorem and needs no $v$-representability. For a molecular potential $v=-\sum_AZ_A|r-R_A|^{-1}$ the $v$-admissible states are exactly the normalized elements of $\mathcal A_N(R)$, and the left side is the electronic ground-state energy.

## Depends on

- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)

## Proof depends on

None.

## Expansion

The potential term $\int v\rho_\Psi$ and the admissibility condition $\int|v|\rho_\Psi<\infty$ depend on $\Psi$ only through $\rho_\Psi$, so the infimum over states splits over the fibres of the density map: $\inf_\Psi=\inf_\rho\inf_{\Psi\mapsto\rho}$. Every admissible state has a density in $\mathcal D_N$ by definition, so no state is missed. For the molecular potential, $\int|v|\rho_\Psi$ is the sum of the nuclear integrals of the energy form.

## Sources

- Mathieu Lewin, Elliott H. Lieb and Robert Seiringer, *Universal Functionals in Density Functional Theory*, chapter in *Density Functional Theory — Modeling, Mathematical Analysis, Computational Methods, and Applications*; numbers from arXiv:1912.10424v4, §1, Eqs. (6)–(7) (two-step minimization and the Levy–Lieb functional). <https://arxiv.org/abs/1912.10424v4>
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §VI.B 'Hohenberg-Kohn theorems' (Levy's proof, pp. 47–49). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
