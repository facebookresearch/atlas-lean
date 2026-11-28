# Full configuration interaction energy

The full configuration interaction energy is the minimum of the electronic energy over the span of all Slater determinants of a finite spin-orbital basis; its difference from the Hartree–Fock energy in the same basis is the correlation energy.

Fix nuclei, an orthonormal family $\varphi_1,\dots,\varphi_M$ of admissible spin-orbitals with finite pair integrals, and $1\le N\le M$. Let $V_N$ be the $\binom MN$-dimensional span of the Slater determinants of $N$ distinct $\varphi_j$. The full configuration interaction (FCI) energy is

$$
E_{\mathrm{FCI}}=\min\{E_R(\Psi):\Psi\in V_N,\ \|\Psi\|=1\},
$$

the smallest eigenvalue of the Hermitian matrix of the electronic energy form on the determinant basis of $V_N$ (the finite compression of the form), equivalently of the second-quantized Hamiltonian on the $N$-particle sector of $\mathcal F_M$. With $E_{\mathrm{HF}}^{V}$ the infimum of $E_R$ over Slater determinants of orthonormal orbitals in $\mathrm{span}\{\varphi_j\}$, the correlation energy in this basis is $E_{\mathrm{corr}}=E_{\mathrm{FCI}}-E_{\mathrm{HF}}^{V}\le0$. For $N=M$ the space is one-dimensional and $E_{\mathrm{corr}}=0$. Nothing is asserted about the continuum problem: a finite FCI energy is an upper bound for the form infimum, not an attained continuum eigenvalue.

## Context

Undergraduate/graduate. FCI is the target that variational and phase-estimation quantum algorithms aim to reproduce, since its classical cost grows with $\binom MN$; the review of Cao, Aspuru-Guzik and coauthors uses the FCI dissociation curve of the hydrogen molecule in a minimal basis as its benchmark.

## Depends on

- [Energy form of Slater determinants](../slater-determinants-and-second-quantization/energy-form-of-slater-determinants.md)
- [Matrix elements of the second-quantized Hamiltonian](../slater-determinants-and-second-quantization/second-quantized-hamiltonian-matrix-elements.md)
- [Energy of a Slater determinant](../hartree-fock-theory/hartree-fock-energy-of-a-determinant.md)

## Proof depends on

- [Variational principle for the smallest eigenvalue](../../../Physics/quantum-mechanics/postulates-of-finite-dimensional-quantum-mechani/inf-eigenvalues-le-expectation-value.md)

## Expansion

The determinants are an orthonormal basis of $V_N$, so $E_R$ on unit vectors of $V_N$ is the Rayleigh quotient of a Hermitian matrix $A$. The variational principle gives $E_R(\Psi)\ge\lambda_{\min}(A)$, and a unit eigenvector for $\lambda_{\min}(A)$ (spectral theorem for Hermitian matrices; Mathlib `Matrix.IsHermitian.eigenvectorBasis`) attains it, so the minimum exists. Every determinant of orthonormal orbitals $\psi_i=\sum_pc_{pi}\varphi_p$ in the span lies in $V_N$: expanding by multilinearity of the determinant gives a sum of determinants of basis orbitals, those with a repeated orbital vanish, and the rest are $\pm$ basis determinants of $V_N$. This gives $E_{\mathrm{FCI}}\le E_{\mathrm{HF}}^{V}$.

## Sources

- Yudong Cao, Jonathan Romero, Jonathan P. Olson, Matthias Degroote, Peter D. Johnson, Mária Kieferová, Ian D. Kivlichan, Tim Menke, Borja Peropadre, Nicolas P. D. Sawaya, Sukin Sim, Libor Veis and Alán Aspuru-Guzik, *Quantum Chemistry in the Age of Quantum Computing*, Chem. Rev. 119 (2019) 10856–10915, <https://doi.org/10.1021/acs.chemrev.8b00803>; numbers from arXiv:1812.09976v2, §2.1 (FCI expansion) and Appendix C.2 (Fig. 10). <https://arxiv.org/abs/1812.09976v2>
- Krzysztof Szalewicz et al., *Advanced Molecular Science: Electronic Structure Theory*, lecture notes, University of Delaware (dated December 17, 2017), §VII.A (pp. 59–61). [physics.udel.edu/~szalewic/teach/838-17/lectures.pdf](https://www.physics.udel.edu/~szalewic/teach/838-17/lectures.pdf)
