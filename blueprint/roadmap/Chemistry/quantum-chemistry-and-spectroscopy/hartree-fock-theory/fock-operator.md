# Fock operator

The Fock operator of an occupied set of orbitals is the one-electron Hamiltonian plus the Coulomb-minus-exchange potential of the occupied orbitals; it is defined here as a Hermitian form on a linear space of admissible orbitals, and canonical Hartree–Fock orbitals are its nonzero weak eigenfunctions.

Fix nuclei and an orthonormal family $\varphi_1,\dots,\varphi_N$ ($N\ge1$) of admissible spin-orbitals with finite pair integrals. Let $\mathcal D_F$ be the set of admissible spin-orbitals $\chi$ with $\iint|\chi(x_1)|^2|\varphi_j(x_2)|^2|r_1-r_2|^{-1}dx_1dx_2<\infty$ for every $j$ (mixed integrals with the occupied orbitals), and let $\mathcal D\subseteq\mathcal D_F$ be the subset of those $\chi$ whose self-pair integral $\iint|\chi(x_1)|^2|\chi(x_2)|^2|r_1-r_2|^{-1}dx_1dx_2$ is also finite (the trial orbitals of the variational pages). $\mathcal D_F$ is a complex vector space containing the occupied orbitals. For $\chi,\xi\in\mathcal D_F$ the Fock form is

$$
f(\chi,\xi)=h(\chi,\xi)+\sum_{j=1}^{N}\Bigl(\iint\frac{\overline{\chi(x_1)}\,\xi(x_1)\,|\varphi_j(x_2)|^2}{|r_1-r_2|}dx_1dx_2-\iint\frac{\overline{\chi(x_1)}\,\varphi_j(x_1)\,\overline{\varphi_j(x_2)}\,\xi(x_2)}{|r_1-r_2|}dx_1dx_2\Bigr),
$$

with $h$ the one-electron form; all integrals converge absolutely and $f$ is a Hermitian sesquilinear form on $\mathcal D_F$. For a Schwartz-class $\xi\in\mathcal D_F$, $f(\chi,\xi)=\langle\chi,\hat F\xi\rangle$ with $\hat F=-\frac12\nabla^2+v+\sum_j(\hat J_j-\hat K_j)$. A **nonzero** $\psi\in\mathcal D$ is a (weak) eigenfunction of the Fock operator with orbital energy $\varepsilon$ if $f(\chi,\psi)=\varepsilon\langle\chi,\psi\rangle$ for all $\chi\in\mathcal D$; the occupied orbitals are **canonical Hartree–Fock orbitals** if each $\varphi_i$ is such an eigenfunction, with energy $\varepsilon_i$. Properties: $f(\varphi_i,\varphi_i)=h_{ii}+\sum_j(J_{ij}-K_{ij})$; $\mathcal D_F$, $\mathcal D$ and $f$ are unchanged when the occupied orbitals are replaced by $\sum_ju_{ji}\varphi_j$ with $u$ unitary.

## Context

Undergraduate (operator) and graduate (form). The self-consistent-field method solves for occupied orbitals that are eigenfunctions of their own Fock operator. Testing the eigen equation against the trial set $\mathcal D$ is a family of equations, matching the replacement trials used for the Hartree–Fock equations.

## Depends on

- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)
- [Coulomb and exchange integrals](coulomb-and-exchange-integrals.md)
- [Slater–Condon rules for two-electron operators](../slater-determinants-and-second-quantization/slater-condon-rules-two-electron.md)

## Proof depends on

None.

## Expansion

Linearity of $\mathcal D_F$: admissible spin-orbitals form a vector space and $|\chi+\xi|^2\le2|\chi|^2+2|\xi|^2$. Absolute convergence: the direct integrand is bounded by $\frac12(|\chi|^2+|\xi|^2)(x_1)|\varphi_j(x_2)|^2|r_1-r_2|^{-1}$ and the exchange integrand by $\frac12(|\chi(x_1)|^2|\varphi_j(x_2)|^2+|\varphi_j(x_1)|^2|\xi(x_2)|^2)|r_1-r_2|^{-1}$, both integrable for $\chi,\xi\in\mathcal D_F$; no self-pair integral is needed. Hermiticity: conjugate and swap $x_1\leftrightarrow x_2$ in the exchange term. Rotation invariance: the conditions defining $\mathcal D_F$ are equivalent to finiteness of $\iint|\chi(x_1)|^2\rho_{\mathrm{occ}}(x_2)|r_1-r_2|^{-1}$ with $\rho_{\mathrm{occ}}=\sum_j|\varphi_j|^2$ (a sum of nonnegative terms), and both sums in $f$ depend on the occupied orbitals only through $\gamma(x,y)=\sum_j\varphi_j(x)\overline{\varphi_j(y)}$; $\rho_{\mathrm{occ}}$ and $\gamma$ are unitarily invariant. Taking $\chi=\xi=\varphi_i$ gives $J_{ij}$ and $K_{ij}$.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.C, Eq. (32) and the unitary invariance of $\hat J$, $\hat K$ (pp. 22–27). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Volker Bach, Elliott H. Lieb, Michael Loss and Jan Philip Solovej, *There are no unfilled shells in unrestricted Hartree-Fock theory*, Phys. Rev. Lett. 72 (1994) 2981–2983, <https://doi.org/10.1103/PhysRevLett.72.2981>; numbers from arXiv:cond-mat/9307066v1, Eqs. (3)–(4). <https://arxiv.org/abs/cond-mat/9307066v1>
