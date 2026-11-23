# Largest and smallest eigenvalues of a Hermitian matrix

For a real or complex Hermitian matrix $A$ indexed by a nonempty finite set, with real eigenvalues $\lambda_i(A)$ listed with multiplicity, the largest eigenvalue is $\lambda_{\max}(A) = \max_i \lambda_i(A)$ and the smallest is $\lambda_{\min}(A) = \min_i \lambda_i(A)$.

## Idea

The eigenvalues of a Hermitian matrix are real, so they can be ordered, and the extreme ones carry most of the information used in analysis: $\lambda_{\max}(A) = \max_{\|u\| = 1} \langle u, Au \rangle$ and $\lambda_{\min}(A) = \min_{\|u\| = 1} \langle u, Au \rangle$, the outer cases of the Courant–Fischer theorem. Every eigenvalue lies between them, and both are attained. For a positive semidefinite matrix, $\lambda_{\max}$ is the spectral norm, the largest factor by which $A$ stretches a vector, and it is at most the trace. Matrix concentration inequalities are stated as bounds on $\lambda_{\max}$ of a random Hermitian matrix.

## Statements

- [Largest eigenvalue](lambda-max.md)
- [Smallest eigenvalue](lambda-min.md): the smallest eigenvalue
- [Every eigenvalue is at most the largest eigenvalue](eigenvalues-le-lambda-max.md): every eigenvalue is at most $\lambda_{\max}$
- [Every eigenvalue is at least the smallest eigenvalue](lambda-min-le-eigenvalues.md): every eigenvalue is at least $\lambda_{\min}$
- [The largest eigenvalue is attained](exists-eigenvalues-eq-lambda-max.md): $\lambda_{\max}$ is attained
- [The smallest eigenvalue is attained](exists-eigenvalues-eq-lambda-min.md): $\lambda_{\min}$ is attained
- [Smallest eigenvalue at most largest eigenvalue](lambda-min-le-lambda-max.md): $\lambda_{\min} \le \lambda_{\max}$
- [Trace dominates each eigenvalue of a positive-semidefinite matrix](eigenvalues-le-re-trace.md): for positive semidefinite matrices, the trace bounds every eigenvalue
- [Hermitian matrices have real-rooted characteristic polynomials](charpoly-is-real-rooted.md): the characteristic polynomial is real-rooted, used for the spectral norm
- [Spectral norm of a positive semidefinite matrix](l2-op-norm-eq-max-real-root-charpoly.md): the spectral norm of a positive semidefinite matrix is its largest eigenvalue
