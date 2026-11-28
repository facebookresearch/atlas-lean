# Hartree–Fock equations

If the energy of a Slater determinant is stationary under all orthonormality-preserving variations of its orbitals, the orbitals satisfy the weak Hartree–Fock equations, and a unitary rotation of the occupied orbitals brings them to canonical form.

Fix nuclei and an orthonormal family $\varphi_1,\dots,\varphi_N$ ($N\ge1$) of admissible spin-orbitals with finite pair integrals, with Slater determinant $\Phi$, and let $\mathcal D$ be the set of admissible spin-orbitals $\chi$ whose pair integrals with $\chi$ itself and with every $\varphi_j$ are finite. For $\chi\in\mathcal D$ orthogonal to all $\varphi_j$ and $i\in\{1,\dots,N\}$, let $\Phi_t$ be the determinant of $\varphi_1,\dots,\varphi_i+t\chi,\dots,\varphi_N$ ($t\in\mathbb R$). Call $\Phi$ **stationary** if

$$
\frac{d}{dt}\Big|_{t=0}\frac{E_R(\Phi_t)}{\|\Phi_t\|^2}=0\qquad\text{for all such }\chi\text{ and }i .
$$

This holds in particular if each of these functions of $t$ has a local minimum at $t=0$, for example if $\Phi$ minimizes $E_R$ among determinants of orthonormal admissible orbitals with finite pair integrals. If $\Phi$ is stationary, then, with $f$ the Fock form of the occupied orbitals,

$$
f(\chi,\varphi_i)=\sum_{j=1}^{N}\varepsilon_{ji}\,\langle\chi,\varphi_j\rangle\quad\text{for all }\chi\in\mathcal D,\qquad \varepsilon_{ji}=f(\varphi_j,\varphi_i),
$$

the matrix $(\varepsilon_{ji})$ is Hermitian, and for a unitary $u$ diagonalizing it the orbitals $\varphi_i'=\sum_ju_{ji}\varphi_j$ are canonical Hartree–Fock orbitals with the same determinant up to the phase $\det u$. These are the equations in weak form; the strong operator form $\hat F\varphi_i=\varepsilon_i\varphi_i$ needs an additional regularity argument.

## Context

Undergraduate (equations) and graduate (variational justification). The self-consistent-field solution is the reference for correlated methods and for the quantum algorithms reviewed by Cao, Aspuru-Guzik and coauthors.

## Depends on

- [Fock operator](fock-operator.md)
- [Energy of a Slater determinant](hartree-fock-energy-of-a-determinant.md)

## Proof depends on

- [Energy form of Slater determinants](../slater-determinants-and-second-quantization/energy-form-of-slater-determinants.md)

## Expansion

By multilinearity of the determinant, $\Phi_t=\Phi+t\Psi$ with $\Psi$ the determinant in which $\varphi_i$ is replaced by $\chi$ in the same row, and $\|\Phi_t\|^2=1+t^2\|\chi\|^2$ because $\chi$ is orthogonal to the occupied orbitals. Sesquilinearity gives $E_R(\Phi_t)=E_R(\Phi)+2t\operatorname{Re}\mathcal E_R(\Psi,\Phi)+O(t^2)$, so the derivative is $2\operatorname{Re}\mathcal E_R(\Psi,\Phi)$. The single-replacement case of the energy-form lemma (applied after normalizing $\chi$) gives $\mathcal E_R(\Psi,\Phi)=f(\chi,\varphi_i)$. Replacing $\chi$ by $i\chi$ kills the imaginary part, so $f(\chi,\varphi_i)=0$ for $\chi\perp\varphi_1,\dots,\varphi_N$; decomposing a general $\chi$ into its occupied component and the rest gives the displayed equation. Hermiticity is that of $f$; the rotated orbitals have the same Fock form by unitary invariance.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §IV.C, Eq. (32) and the canonical form (pp. 22–27). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Volker Bach, Elliott H. Lieb, Michael Loss and Jan Philip Solovej, *There are no unfilled shells in unrestricted Hartree-Fock theory*, Phys. Rev. Lett. 72 (1994) 2981–2983, <https://doi.org/10.1103/PhysRevLett.72.2981>; numbers from arXiv:cond-mat/9307066v1, Eqs. (3)–(4). <https://arxiv.org/abs/cond-mat/9307066v1>
