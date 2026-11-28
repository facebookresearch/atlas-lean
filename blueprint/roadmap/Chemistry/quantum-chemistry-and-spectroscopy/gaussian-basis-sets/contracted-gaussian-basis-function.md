# Contracted Gaussian basis function

A contracted Cartesian Gaussian basis function is a fixed linear combination of Gaussian primitives sharing one centre and one angular part; these are the standard one-electron basis functions of molecular quantum chemistry.

A primitive Cartesian Gaussian with exponent $\alpha>0$ (units of inverse length squared), centre $A\in\mathbb R^3$ and angular exponents $a=(a_x,a_y,a_z)\in\mathbb N^3$ is

$$
g(r;\alpha,A,a)=(x-A_x)^{a_x}(y-A_y)^{a_y}(z-A_z)^{a_z}\,e^{-\alpha|r-A|^2},\qquad r=(x,y,z),
$$

with angular momentum $\ell=a_x+a_y+a_z$. A contracted Gaussian with $K\ge1$ primitives is $\chi(r)=\sum_{k=1}^{K}c_k\,g(r;\alpha_k,A,a)$ with real contraction coefficients $c_k$ and exponents $\alpha_k>0$; distinct exponents are a common nonredundancy convention, not a requirement. Every Cartesian contraction is a Schwartz function, hence lies in $H^1(\mathbb R^3)$. Spherical Gaussian-type orbitals use a radial factor $N\,r^{n-1}e^{-\zeta r^2}$ times a spherical harmonic $Y_{\ell m}$; they are Schwartz functions when $n-1-\ell$ is a nonnegative even integer (a solid harmonic times a polynomial in $|r|^2$), but not in general: for $n=2$, $\ell=0$ the function $|r|e^{-\zeta|r|^2}Y_{00}$ is not differentiable at the centre. Being nonzero and linearly independent are separate conditions on a family of contractions.

## Context

Undergraduate. Gaussian functions replace Slater-type orbitals because their integrals are analytic (Gaussian product theorem), at the price of a missing nuclear cusp; the minimal STO-$n$G bases of small quantum-computing demonstrations are of this form.

## Depends on

- [Sobolev space $H^1(U)$](../../../Analysis/partial-differential-equations/weak-solutions-of-elliptic-equations/mem-h1-on.md)

## Proof depends on

None.

## Expansion

A definition. Polynomials times Gaussians are smooth and decay faster than any power together with all derivatives. The one-electron integrals with nuclear attraction are finite because the integrand is bounded times $|r-R_A|^{-1}$, which is locally integrable in $\mathbb R^3$, and decays rapidly; electron-repulsion integrals are finite for the same reason. The parameters are those listed by Tamayo-Mendoza and coauthors: exponents, contraction coefficients, centres and angular exponents.

## Sources

- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, Appendix A, Eqs. (88)–(90) and the following discussion of Cartesian Gaussians and contractions. <https://arxiv.org/abs/1812.09976v2>
- Teresa Tamayo-Mendoza, Christoph Kreisbeck, Roland Lindh and Alán Aspuru-Guzik, *Automatic Differentiation in Quantum Chemistry with Applications to Fully Variational Hartree–Fock*, ACS Cent. Sci. 4 (2018) 559–566, <https://doi.org/10.1021/acscentsci.7b00586> (PMC5968443), section 'Fully Variational Hartree–Fock', parameters (i)–(iv).
