# Determinant of the matrix exponential

For every complex square matrix $A$ indexed by a finite set, $\det(e^A) = e^{\operatorname{tr} A}$, where $e^A = \sum_{k \ge 0} A^k / k!$ is the matrix exponential.

## Idea

If $A$ is diagonal with entries $\lambda_i$, then $e^A$ is diagonal with entries $e^{\lambda_i}$, and both sides equal $e^{\sum \lambda_i}$. The general case reduces to this one: the exponential respects similarity, so one may triangularize $A$, and the diagonal of $e^T$ for triangular $T$ is the exponential of the diagonal of $T$. The identity shows that $e^A$ is always invertible and that the exponential maps trace-zero matrices to matrices of determinant one, which links the Lie algebra $\mathfrak{sl}_n$ to the group $\mathrm{SL}_n$. The two other statements supply steps of such an argument: the exponential respects similarity, and the exponential of a nilpotent matrix has determinant $1$.

## Statements

- [Determinant of the matrix exponential](matrix-det-exp-eq-exp-trace.md)
- [Exponential of a nilpotent matrix](matrix-exp-eq-sum-of-is-nilpotent.md): for nilpotent $A$, $e^A$ is a finite sum, the identity plus a nilpotent matrix, so its determinant is $1 = e^{\operatorname{tr} A}$, the step for nilpotent matrices
- [Intertwining passes to the exponential](exp-mul-eq-mul-exp-of-mul-eq.md): $AX = XB$ gives $e^A X = X e^B$; for invertible $X$, similar matrices have similar exponentials, which lets the argument pass to a triangular form

## Sources

- B. C. Hall, Lie Groups, Lie Algebras, and Representations, 2nd ed., Springer (2015), Chapter 2.

## Related topics

- [Eigenvalues and spectral norm of Hermitian matrices](../../eigenvalues-and-canonical-forms/eigenvalues-and-spectral-norm-of-hermitian-matri/README.md)
