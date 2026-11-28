# Roothaan–Hall equations

Projecting the canonical Hartree–Fock equations onto a finite basis gives a nonlinear generalized Hermitian eigenvalue problem $FC=SC\varepsilon$ for the orbital coefficients.

Fix an occupied orthonormal family as for the Fock operator, with Fock form $f$ on $\mathcal D$. Let $\chi_1,\dots,\chi_K\in\mathcal D$ be linearly independent, with overlap matrix $S_{\mu\nu}=\langle\chi_\mu,\chi_\nu\rangle$ (Hermitian positive definite) and Fock matrix $F_{\mu\nu}=f(\chi_\mu,\chi_\nu)$ (Hermitian). For a spin-orbital $\psi=\sum_\nu c_\nu\chi_\nu$ with $c\in\mathbb C^K\setminus\{0\}$ and $\varepsilon\in\mathbb R$, the Galerkin-projected eigen equation $f(\chi_\mu,\psi)=\varepsilon\langle\chi_\mu,\psi\rangle$ for all $\mu$ is equivalent to

$$
Fc=\varepsilon\,Sc ,\qquad\text{and then}\qquad \varepsilon=\frac{c^\dagger Fc}{c^\dagger Sc}.
$$

Collecting $K'\le K$ such columns as $C\in\mathbb C^{K\times K'}$ with $C^\dagger SC=\mathbf 1$ and $\varepsilon=\mathrm{diag}(\varepsilon_1,\dots,\varepsilon_{K'})$ gives $FC=SC\varepsilon$. When the occupied orbitals are themselves the first $N$ columns, $F$ depends on $C$ and the problem is nonlinear (self-consistent). This is the projected, not the unprojected continuum, equation.

## Context

Undergraduate. The self-consistent-field procedure iterates this generalized eigenproblem. For closed-shell restricted orbitals (each spatial orbital occupied with both spins) the two spin blocks coincide and one obtains the spatial Roothaan equations with $N/2$ doubly occupied columns; the Pariser–Parr–Pople model is a semiempirical instance of that spatial form.

## Depends on

- [Fock operator](fock-operator.md)
- [Hartree–Fock equations](hartree-fock-equations.md)

## Proof depends on

None.

## Expansion

Substitute the expansion into $f(\chi_\mu,\psi)=\varepsilon\langle\chi_\mu,\psi\rangle$ and use linearity in the second argument; this is $(Fc)_\mu=\varepsilon(Sc)_\mu$ for all $\mu$. Multiplying by $c^\dagger$ gives $c^\dagger Fc=\varepsilon\,c^\dagger Sc$, and $c^\dagger Sc=\|\psi\|^2>0$ for $c\ne0$ by linear independence. The real-symmetric generalized Rayleigh-quotient pages of this field are the real special case.

## Sources

- C. David Sherrill, *An Introduction to Hartree-Fock Molecular Orbital Theory*, lecture notes, School of Chemistry and Biochemistry, Georgia Institute of Technology (June 2000), §7, Eqs. (28)–(35). [vergil.chemistry.gatech.edu/static/content/hf-intro.pdf](https://vergil.chemistry.gatech.edu/static/content/hf-intro.pdf)
- Kjell Jorner, Robert Pollice, Cyrille Lavigne and Alán Aspuru-Guzik, *Ultrafast Computational Screening of Molecules with Inverted Singlet–Triplet Energy Gaps Using the Pariser–Parr–Pople Semiempirical Quantum Chemistry Method*, J. Phys. Chem. A 128 (2024) 2445–2456, <https://doi.org/10.1021/acs.jpca.3c06357> (PMC10983003), Eq. (1).
