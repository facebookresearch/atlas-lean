# Characteristic polynomial

Let $V$ be a nonzero finite-dimensional vector space over $\mathbb F = \mathbb R$ or $\mathbb C$ and $T \colon V \to V$ a
linear map. The characteristic polynomial of $T$ is the polynomial $z \mapsto \det(zI - T)$, where $I$ is the identity
map; it is monic of degree $\dim V$.

## Idea

Its zeros in $\mathbb F$ are exactly the eigenvalues of $T$: $\lambda$ is an eigenvalue when $\lambda I - T$ is not
invertible, that is, when $\det(\lambda I - T) = 0$. In a basis in which $T$ has matrix $A$, it is $\det(zI - A)$, and
for $n = \dim V$ it reads $z^n - (\operatorname{tr} T) z^{n-1} + \dots + (-1)^n \det T$; for a $2 \times 2$ matrix with
rows $(a, b)$ and $(c, d)$ it is $z^2 - (a + d) z + (ad - bc)$. Over $\mathbb C$ it factors as
$(z - \lambda_1)^{d_1} \cdots (z - \lambda_m)^{d_m}$, where $\lambda_1, \dots, \lambda_m$ are the distinct eigenvalues
and $d_k$ is the multiplicity of $\lambda_k$. The [Cayley–Hamilton theorem](../cayley-hamilton-theorem/aeval-self-charpoly.md) says that $T$ is a zero of its characteristic
polynomial. Some books use $\det(T - zI)$, which is $(-1)^n$ times this polynomial and has the same zeros.

## Statements

- [Characteristic polynomial of an operator](characteristic-polynomial.md)
- [Eigenvalues are the roots of the characteristic polynomial](has-eigenvalue-iff-is-root-charpoly.md): why the polynomial matters: its roots are exactly the eigenvalues, here for free modules of finite rank over an integral domain

## Background

- [Eigenvalues and eigenvectors](../../eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/README.md): eigenvalues
- [Determinant of a linear map](../../../determinants-and-matrix-identities/determinants-of-linear-maps/determinant-of-a-linear-map/README.md): the determinant in the definition
- [Leibniz formula for the determinant](../../../determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/README.md): used to show that the polynomial is monic of degree $\dim V$

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 9.63, with 9.51, 9.62 and 9.65 (version read: the open-access PDF dated 4 November 2026).
