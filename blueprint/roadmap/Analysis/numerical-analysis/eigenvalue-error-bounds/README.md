# Eigenvalue error bounds

A posteriori bounds for computed eigenvalues: for a Hermitian matrix, a unit vector $\tilde u$ with residual $r = A\tilde u - \tilde\lambda \tilde u$ certifies an eigenvalue within $\|r\|_2$ of $\tilde\lambda$, and when $\tilde\lambda$ is the Rayleigh quotient the error is of order $\|r\|_2^2$ divided by the spectral gap (Kato–Temple). The power method produces such approximations for the dominant eigenvalue; its analysis for a general matrix uses the spectral projectors onto the generalized eigenspaces, and Gerschgorin's discs and Wielandt deflation locate and separate eigenvalues.

- [Residual bound for eigenvalues of a Hermitian matrix](residual-bound-for-hermitian-eigenvalues.md)
- [Residual bound on an eigenvalue-free interval around a Rayleigh quotient](rayleigh-quotient-residual-lemma.md)
- [Kato–Temple inequality](kato-temple-inequality.md)
- [Rayleigh quotient error and the spectral gap](rayleigh-quotient-error-and-the-spectral-gap.md)
- [Residual bound on the angle to an eigenspace](eigenvector-angle-residual-bound.md)
- [An isolated union of Gerschgorin discs holds as many eigenvalues as discs](gerschgorin-discs-isolated-union-counts-eigenvalues.md)

## The power method

- [Spectral projectors of a square matrix](spectral-projectors.md)
- [Spectral decomposition of a square matrix](spectral-decomposition-of-a-square-matrix.md)
- [Rate of convergence of the power iterates](power-iterates-converge-at-the-rate-of-the-subdominant-eigenvalues.md)
- [Convergence of the power method](convergence-of-the-power-method.md)
- [Convergence of the power method with max-component normalization](normalized-power-method-converges.md)
- [Convergence of subspace iteration](subspace-iteration-converges.md)
- [Wielandt deflation](wielandt-deflation.md)
- [Gerschgorin's circle theorem](gerschgorin-circle-theorem.md)

## Related topics

- [Power iteration](../../../LinearAlgebra/eigenvalues-and-canonical-forms/power-iteration-and-the-rayleigh-quotient/README.md): the symmetric case of the power method, with linear convergence of the iterates and quadratic accuracy of the Rayleigh quotient.
- [Bauer–Fike theorem](../../operator-theory/eigenvalue-inequalities/bauer-fike-theorem/README.md): perturbation bounds for the spectrum.
- [Arnoldi and Lanczos iterations](../../../LinearAlgebra/matrix-decompositions/arnoldi-and-lanczos-iterations/README.md): Krylov methods, whose Ritz values these bounds assess.
