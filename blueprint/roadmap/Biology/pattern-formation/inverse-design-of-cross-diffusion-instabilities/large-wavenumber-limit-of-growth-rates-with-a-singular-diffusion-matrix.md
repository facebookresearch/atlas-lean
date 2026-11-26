# Large-wavenumber limit of growth rates with a singular diagonalisable diffusion matrix

**Setting.** Linearising a reaction–cross-diffusion system $\partial_t u = f(u) + \partial_x\big(D(u)\,\partial_x u\big)$, $u \in \mathbb{R}^n$, at a homogeneous steady state gives $\partial_t u_1 = J u_1 + \hat D\,\partial_{xx}u_1$ with constant $J, \hat D \in \mathbb{R}^{n \times n}$. Laplacian eigenmodes with eigenvalue $\mu = k^2 \ge 0$ grow like $e^{\lambda t}$ where

$$\det\big(J - \mu\hat D - \lambda I\big) = 0 .$$

**Lemma 1.** Let $\hat D$ be diagonalisable, $D = Q^{-1}\hat D Q$ diagonal, with exactly $\ell$ eigenvalues $\sigma_{i_1} = \dots = \sigma_{i_\ell} = 0$ and all other eigenvalues positive. As $\mu \to \infty$:

- $\ell$ eigenvalues of $J - \mu\hat D$ converge to the eigenvalues of the principal submatrix of $Q^{-1}JQ$ formed by rows and columns $i_1,\dots,i_\ell$;
- the real parts of the remaining $n - \ell$ eigenvalues tend to $-\infty$.

In particular, if that principal submatrix of $Q^{-1}JQ$ has an eigenvalue with positive real part, then $J - \mu\hat D$ has an eigenvalue with positive real part for all large $\mu$; replacing the zero eigenvalues of $\hat D$ by small $\delta > 0$ preserves this on a bounded interval of $\mu$ by continuity, which yields a finite band of unstable wavenumbers.

## Expansion

Conjugating by $Q$ replaces $J - \mu\hat D$ by $K - \mu D$ with $K = Q^{-1}JQ$, and $D$ diagonal with zeros exactly at positions $i_1,\dots,i_\ell$. Writing $K - \mu D$ in block form with respect to these positions, the block of the zero-diffusion components is $\mu$-independent, while the complementary diagonal block is $K_{22} - \mu D_{22}$ with $D_{22}$ positive diagonal. Dividing the characteristic polynomial by $\mu^{n-\ell}$ and letting $\mu \to \infty$, a Schur-complement argument shows that $n - \ell$ eigenvalues behave like $-\mu\sigma_i + O(1)$ and the other $\ell$ converge to the spectrum of $K_{11}$. If $\ell = n$ then $\hat D = 0$ and the spectrum is that of $J$ for every $\mu$. The lemma generalises the classical observation for diagonal diffusion that a non-diffusing species with an unstable self-interaction destabilises small scales.

## Sources

- E. Villar-Sepúlveda, A. R. Champneys, A. L. Krause, "Designing reaction-cross-diffusion systems with Turing and wave instabilities", Journal of Mathematical Biology (2025), Eqs. (1)–(3) and Lemma 1, <https://doi.org/10.1007/s00285-025-02274-1>, PMCID PMC12426155.
