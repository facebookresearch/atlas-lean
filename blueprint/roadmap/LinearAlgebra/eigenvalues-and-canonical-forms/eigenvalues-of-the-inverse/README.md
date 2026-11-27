# Eigenvalues of the inverse matrix

Let $M$ be a square matrix over a field $K$, indexed by a finite set, with $\det M \ne 0$, and let $\mu \in K$ be nonzero. Then $x$ is an eigenvector of $M$ with eigenvalue $\mu$ ($x \ne 0$ and $Mx = \mu x$) if and only if $x$ is an eigenvector of $M^{-1}$ with eigenvalue $\mu^{-1}$.

## Idea

Multiplying $Mx = \mu x$ by $\mu^{-1} M^{-1}$ gives $M^{-1} x = \mu^{-1} x$, and the converse is the same computation with the roles exchanged. So an invertible matrix and its inverse have the same eigenvectors, with reciprocal eigenvalues; an invertible matrix never has the eigenvalue $0$, so all its eigenvalues can be inverted. Inverse iteration relies on this: a simple eigenvalue of $M$ of strictly smallest modulus becomes the strictly dominant eigenvalue of $M^{-1}$, and under the usual assumptions of power iteration (for example a diagonalizable $M$ and a starting vector with a nonzero component along the corresponding eigenvector) the normalized iterates of $M^{-1}$ approach the line spanned by that eigenvector: up to sign over the reals, and up to a complex factor of modulus $1$ over the complex numbers, where the iterates themselves need not converge (for $M = \operatorname{diag}(i, 2)$ the normalized iterates from $e_1$ are $(-i)^k e_1$). Without a strict gap or with an unlucky start this can fail: for $M = \operatorname{diag}(1, -1)$ the normalized iterates from $(1, 1)$ alternate.

## Statements

- [Eigenvalues of the inverse matrix](inverse-eigenvalues.md)
