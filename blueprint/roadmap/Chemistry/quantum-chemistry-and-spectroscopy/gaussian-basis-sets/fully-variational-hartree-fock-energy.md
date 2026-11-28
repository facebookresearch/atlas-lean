# Fully variational Hartree–Fock energy

The fully variational Hartree–Fock energy minimizes the finite-basis closed-shell Hartree–Fock energy not only over orbital coefficients but also over the exponents, contraction coefficients and centres of the Gaussian basis functions.

Fix nuclei, an even electron number $N=2n$ and a basis template: $K\ge n$ contracted Cartesian Gaussians with fixed angular exponents and fixed numbers of primitives, whose remaining parameters $\theta$ (exponents $\alpha>0$, contraction coefficients, centres in $\mathbb R^3$) range over the set $\Theta$ of values for which the spatial functions $\chi_1(\theta),\dots,\chi_K(\theta)$ are linearly independent. A **closed-shell determinant** in this basis is the Slater determinant of the $2n$ spin-orbitals $\psi_j\otimes\uparrow,\psi_j\otimes\downarrow$ for orthonormal spatial orbitals $\psi_1,\dots,\psi_n\in\mathrm{span}\{\chi_\mu(\theta)\}$. Let $E_{\mathrm{RHF}}(\theta)$ be the infimum of its electronic energy over these choices. The fully variational Hartree–Fock energy is

$$
E_{\mathrm{FV}}=\inf_{\theta\in\Theta}E_{\mathrm{RHF}}(\theta)\in[-\infty,+\infty],
$$

with $E_{\mathrm{FV}}=+\infty$ if $\Theta$ is empty. When only the centres vary this is the floating-Gaussian method. For any fixed standard basis $\theta_0\in\Theta$ of the same template, $E_{\mathrm{FV}}\le E_{\mathrm{RHF}}(\theta_0)$, and $E_{\mathrm{FV}}$ is at least the infimum of the electronic energy over all closed-shell determinants of admissible spatial orbitals. This idealized nested infimum is narrower than every variational parameter the source discusses (nuclear positions are fixed here) and makes no claim that a local optimizer reaches it.

## Context

Graduate. Tamayo-Mendoza, Kreisbeck, Lindh and Aspuru-Guzik compute gradients of $E_{\mathrm{RHF}}(\theta)$ by automatic differentiation and optimize minimal STO-2G/STO-3G templates with BFGS, motivated by compact bases for quantum-computing simulations; their energies are computational results. As background (not used), for each $\theta$ the infimum $E_{\mathrm{RHF}}(\theta)$ is attained: the orthonormal $n$-frames of the span form a compact set, and the energy is a polynomial in the frame coefficients with the finite matrix elements of the basis as coefficients, hence continuous.

## Depends on

- [Contracted Gaussian basis function](contracted-gaussian-basis-function.md)
- [Energy of a Slater determinant](../hartree-fock-theory/hartree-fock-energy-of-a-determinant.md)

## Proof depends on

None.

## Expansion

A definition. The first inequality holds because $\theta_0$ is admissible, the second because every finite-basis closed-shell determinant is admissible for the larger problem (Gaussian contractions are admissible orbitals with finite pair integrals). Nonemptiness of $\Theta$ is not claimed; an empty $\Theta$ gives $+\infty$ by the convention $\inf\emptyset=+\infty$. Lower boundedness of the Coulomb energy form, which would make $E_{\mathrm{FV}}$ finite, is not claimed here.

## Sources

- Teresa Tamayo-Mendoza, Christoph Kreisbeck, Roland Lindh and Alán Aspuru-Guzik, *Automatic Differentiation in Quantum Chemistry with Applications to Fully Variational Hartree–Fock*, ACS Cent. Sci. 4 (2018) 559–566, <https://doi.org/10.1021/acscentsci.7b00586> (PMC5968443), sections 'Fully Variational Hartree–Fock', 'Implementation' and 'Results' (schemes A and B).
