# Any non-scalar stable Jacobian admits a cross-diffusion matrix inducing Turing or wave instability

**Setting.** For the linearised system $\partial_t u_1 = J u_1 + \hat D\,\partial_{xx}u_1$, $u_1 \in \mathbb{R}^n$, $n \ge 2$, growth rates $\lambda$ of the mode with Laplacian eigenvalue $\mu = k^2$ solve $\det(J - \mu\hat D - \lambda I) = 0$. Assume $J$ is stable (all eigenvalues have negative real part) and non-scalar (not a multiple of the identity). The system exhibits

- a *Turing instability* if some $\mu > 0$ gives a real root $\lambda > 0$;
- a *wave instability* if some $\mu > 0$ gives a complex-conjugate pair $\lambda$ with positive real part and non-zero imaginary part.

**Theorem 1.** Let $J$ be a non-scalar stable matrix. Then there is a diagonalisable diffusion matrix $\hat D$ with strictly positive real eigenvalues for which the system exhibits a Turing instability. If moreover $n \ge 3$ and $J$ has at least $\ell$ distinct eigenvalues, $1 \le \ell \le 3$, with at least $3 - \ell$ corresponding generalised eigenvectors, then there is also a diagonalisable diffusion matrix $\hat D$ with strictly positive real eigenvalues for which the system exhibits a wave instability. (As in the source, which assumes throughout that $\hat D$ has strictly positive real eigenvalues and hence is invertible.)

**Theorem 2.** Let $\hat D$ be a non-scalar diagonalisable matrix with strictly positive real eigenvalues. Then there is a stable matrix $J$ for which the system exhibits a Turing instability, and if $n \ge 3$ there is also a stable $J$ for which it exhibits a wave instability.

## Depends on

- [Large-wavenumber limit of growth rates with a singular diagonalisable diffusion matrix](large-wavenumber-limit-of-growth-rates-with-a-singular-diffusion-matrix.md)

## Expansion

For Theorem 1, a non-scalar real matrix has a $2 \times 2$ non-scalar block in its Jordan form, so $J$ is similar to a matrix $K = Q^{-1}JQ$ with a $1 \times 1$ (Turing) or $2 \times 2$ (wave) unstable principal submatrix, even though $K$ itself is stable; the stated condition on distinct eigenvalues and generalised eigenvectors is what allows a $3 \times 3$ or $4 \times 4$ block of $K$ to carry a $2 \times 2$ principal submatrix with complex unstable eigenvalues. Taking $\hat D = Q D Q^{-1}$ with $D$ diagonal, zero on that submatrix and positive elsewhere, the large-wavenumber limit lemma gives a growth rate converging to the unstable eigenvalue, real or complex as required. Relaxing the zero diffusion coefficients to small $\delta > 0$ gives $\hat D$ strictly positive eigenvalues and turns the unbounded unstable range into a finite band, and $\delta$ can be tuned to place the critical wavelength; the marginal value of $\delta$ is a Turing or wave bifurcation point. Theorem 2 runs the construction in reverse: with at least two distinct diffusion eigenvalues one designs $J$, in the eigenbasis of $\hat D$, as a stable matrix with a $2$-component (Turing) or $3$-component (wave) subsystem that is destabilised by the differential diffusion. Wave instabilities need $n \ge 3$ because for $n = 2$ the dispersion relation cannot produce an unstable complex pair at $\mu > 0$ from a stable $J$, even with cross-diffusion.

## Sources

- E. Villar-Sepúlveda, A. R. Champneys, A. L. Krause, "Designing reaction-cross-diffusion systems with Turing and wave instabilities", Journal of Mathematical Biology (2025), Theorems 1–2, Lemmas 1–4 and their proofs, <https://doi.org/10.1007/s00285-025-02274-1>, PMCID PMC12426155.
