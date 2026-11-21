# Eigenvalues and spectral norm of Hermitian matrices

The eigenvalues of a Hermitian matrix are real; the largest and smallest, $\lambda_{\max}$ and $\lambda_{\min}$, control its spectral norm and its semidefinite order. Standard matrix functions $f(A)$ act on the eigenvalues, so $\operatorname{tr} f(A) = \sum_i f(\lambda_i)$. For the exponential this gives $e^{\theta\lambda_{\max}(A)} \le \operatorname{tr} e^{\theta A}$, the deterministic input to the matrix Laplace transform method of matrix concentration.

- [Hermitian matrices have real-rooted characteristic polynomials](charpoly-is-real-rooted.md)
- [Spectral norm of a positive semidefinite matrix](l2-op-norm-eq-max-real-root-charpoly.md)
- [Largest eigenvalue](lambda-max.md)
- [Smallest eigenvalue](lambda-min.md)
- [Every eigenvalue is at most the largest eigenvalue](eigenvalues-le-lambda-max.md)
- [Every eigenvalue is at least the smallest eigenvalue](lambda-min-le-eigenvalues.md)
- [The largest eigenvalue is attained](exists-eigenvalues-eq-lambda-max.md)
- [The smallest eigenvalue is attained](exists-eigenvalues-eq-lambda-min.md)
- [Smallest eigenvalue at most largest eigenvalue](lambda-min-le-lambda-max.md)
- [Trace dominates each eigenvalue of a positive-semidefinite matrix](eigenvalues-le-re-trace.md)
- [Trace of a standard matrix function](trace-cfc-eq-sum.md)
- [The matrix exponential is a standard matrix function](exp-smul-eq-cfc.md)
- [Trace exponential in terms of eigenvalues](trace-exp-smul-eq-sum.md)
- [Real trace exponential in terms of eigenvalues](re-trace-exp-smul-eq-sum.md)
- [Nonnegativity of the trace exponential](re-trace-exp-nonneg.md)
- [Positivity of the trace exponential](re-trace-exp-pos.md)
- [Trace exponential dominates each eigenvalue](exp-mul-eigenvalues-le-re-trace-exp.md)
- [Trace exponential dominates the top eigenvalue](exp-mul-lambda-max-le-re-trace-exp.md)
- [Trace exponential dominates the bottom eigenvalue](exp-mul-lambda-min-le-re-trace-exp.md)
- [Hermitian dilation](dilation.md)
- [The Hermitian dilation is Hermitian](is-hermitian-dilation.md)
- [The Hermitian dilation is additive](dilation-add.md)
- [The Hermitian dilation commutes with real scalars](dilation-smul.md)
- [Square of the Hermitian dilation](dilation-mul-self.md)
- [The spectrum of the Hermitian dilation is symmetric](signature-mul-dilation-mul-signature.md)

## Related topics

- [Matrix exponential](../../determinants-and-matrix-identities/matrix-exponential/README.md)
- [Matrix concentration inequalities](../../../Probability/concentration-inequalities/matrix-concentration-inequalities/README.md)
- [Eigenvalue inequalities and perturbation](../../../Analysis/operator-theory/eigenvalue-inequalities/README.md)
