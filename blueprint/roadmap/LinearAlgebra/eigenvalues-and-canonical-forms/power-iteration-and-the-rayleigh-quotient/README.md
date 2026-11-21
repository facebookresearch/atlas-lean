# Power iteration and the Rayleigh quotient

The simplest eigenvalue algorithm: repeated multiplication by $T$ and normalization. For an operator with an orthonormal eigenbasis (a symmetric matrix), a strictly dominant eigenvalue and a starting vector whose component along the dominant eigenvector is nonzero, the iterates converge to the dominant eigenvector, up to sign, linearly at the rate $|\lambda_2/\lambda_1|$, and the Rayleigh quotient converges to the eigenvalue at the squared rate, because the Rayleigh quotient is a quadratically accurate eigenvalue estimate (Trefethen and Bau, Lecture 27). Inverse iteration, Rayleigh quotient iteration and the QR algorithm refine this idea.

- [Powers of an operator on an eigenvector](pow-apply-of-eigen.md)
- [Coordinates of powers in an eigenbasis](inner-pow-apply.md)
- [Power iteration converges linearly (unnormalized form)](norm-smul-pow-apply-sub-le.md)
- [Normalizing at most doubles the distance to a unit vector](norm-normalize-sub-le.md)
- [Power iteration converges to the dominant eigenvector up to sign](exists-sign-norm-normalize-sub-le.md)
- [Quadratic accuracy of the Rayleigh quotient](inner-apply-sub-eq-of-eigen.md)
- [The power-iteration eigenvalue estimate converges twice as fast](abs-rayleigh-pow-apply-sub-le.md)

## Related topics

- [Arnoldi and Lanczos iterations](../../matrix-decompositions/arnoldi-and-lanczos-iterations/README.md)
- [Principal component analysis](../../../Probability/linear-models-multivariate/principal-component-analysis/README.md)
- [Diagonalization](../diagonalization/README.md)
