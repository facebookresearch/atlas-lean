# Kohn–Sham equations

The Kohn–Sham model represents the electron density by $N$ orthonormal orbitals of a noninteracting system and determines them by self-consistent one-electron equations with an exchange-correlation potential.

Fix nuclei with potential $v(r)=-\sum_AZ_A|r-R_A|^{-1}$ and an exchange-correlation functional $E_{\mathrm{xc}}$, a real function on densities. For orthonormal admissible spin-orbitals $\varphi_1,\dots,\varphi_N$ with density $\rho=\sum_i\sum_s|\varphi_i(r,s)|^2$ (summed over spin) the Kohn–Sham energy is

$$
E_{\mathrm{KS}}[\varphi]=\sum_{i=1}^{N}\frac12\|\nabla\varphi_i\|^2+\int v\rho+\frac12\iint\frac{\rho(r)\rho(r')}{|r-r'|}\,dr\,dr'+E_{\mathrm{xc}}[\rho],
$$

where the Hartree term is assumed finite. Assume $E_{\mathrm{xc}}$ is differentiable along admissible densities with derivative represented by a real function $v_{\mathrm{xc}}$: $\frac{d}{dt}E_{\mathrm{xc}}[\rho_t]|_{t=0}=\int v_{\mathrm{xc}}\,\dot\rho_0$ for densities $\rho_t$ of the orbital variations used below, with $\int|v_{\mathrm{xc}}|(|\varphi|^2+|\chi|^2)<\infty$. The Kohn–Sham equations are the weak stationarity conditions: after a unitary rotation of the orbitals,

$$
\frac12\langle\nabla\chi,\nabla\varphi_i\rangle+\int\Bigl(v+\int\frac{\rho(r')}{|r-r'|}dr'+v_{\mathrm{xc}}\Bigr)\overline\chi\,\varphi_i=\varepsilon_i\langle\chi,\varphi_i\rangle\qquad\text{for all admissible test orbitals }\chi,
$$

to be solved self-consistently. With the LDA, $E_{\mathrm{xc}}[\rho]=\int e_{\mathrm{xc}}(\rho(r))\,dr$ with $e_{\mathrm{xc}}$ an energy per unit volume.

## Context

Graduate. Kohn–Sham density-functional theory is the workhorse of computational chemistry; the choice of $E_{\mathrm{xc}}$ is an approximation whose reliability is chemistry dependent, as the review of Cao, Aspuru-Guzik and coauthors stresses. The exact functional is defined as $E_{\mathrm{xc}}=F_{\mathrm{LL}}-T_s-J$ with $T_s[\rho]$ the infimum of the kinetic energy over single Slater determinants of density $\rho$ (pure-state determinantal constrained search) and $J$ the Hartree term; this definition asserts neither noninteracting $v$-representability nor the existence of a functional derivative for every density.

## Depends on

- [Constrained-search variational principle](constrained-search-variational-principle.md)
- [Electronic energy form](../molecular-hamiltonian-and-born-oppenheimer/electronic-energy-form.md)
- [Coulomb and exchange integrals](../hartree-fock-theory/coulomb-and-exchange-integrals.md)

## Proof depends on

- [Hartree–Fock equations](../hartree-fock-theory/hartree-fock-equations.md)

## Expansion

A model definition with its Euler–Lagrange equations. Vary one orbital along $\varphi_i+t\chi$ with $\chi$ orthogonal to the occupied orbitals, normalize as in the Hartree–Fock stationarity argument, and differentiate: the kinetic, external and Hartree terms give the displayed form (the factor $\frac12$ of the Hartree energy produces a single Hartree potential), and the exchange-correlation term gives $2\operatorname{Re}\int v_{\mathrm{xc}}\overline\chi\varphi_i$ by the differentiability assumption. Replacing $\chi$ by $i\chi$ and diagonalizing the Hermitian multiplier matrix by a unitary rotation, which leaves $\rho$ unchanged, gives canonical form. Missing prerequisites on the graph: finiteness of the Hartree and potential terms for admissible orbitals and the chain rule for the density along orbital variations.

## Sources

- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §VI.C 'Kohn-Sham method' (pp. 49–53) and §VI.D (local density approximation). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.1 (density functional theory and exchange-correlation functionals). <https://arxiv.org/abs/1812.09976v2>
