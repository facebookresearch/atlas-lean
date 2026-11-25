# Eigenvalues and eigenvectors

Let $R$ be a commutative ring, $M$ an $R$-module and $f \colon M \to M$ an $R$-linear map. A vector $x \in M$ is an
eigenvector of $f$ with eigenvalue $\mu \in R$ when $x \neq 0$ and $x$ lies in the eigenspace $\ker(f - \mu \cdot 1)$,
that is, $f(x) = \mu x$. A scalar is an eigenvalue of $f$ when its eigenspace is not zero, that is, when it has an
eigenvector. These are the general forms of the definitions for a linear operator $T$ on a vector space $V$ over a
field $F$: take $R = F$, $M = V$ and $f = T$; then $v$ is an eigenvector when $v \neq 0$ and $T v = \lambda v$, and
$\lambda$ is an eigenvalue when such a $v$ exists.

## Idea

On the line spanned by an eigenvector, $f$ acts as multiplication by the eigenvalue. For a vector space $V$ of finite
dimension $n$, a scalar $\mu$ is an eigenvalue exactly when $f - \mu \cdot 1$ is not injective, equivalently not
invertible, and the matrix of $f$ in a basis is diagonal exactly when the basis consists of eigenvectors. Eigenvectors
for distinct eigenvalues are linearly independent, so $f$ has at most $n$ eigenvalues. For example, on $\mathbb R^2$
the map $(x, y) \mapsto (y, x)$ has the eigenvector $(1, 1)$ for $1$ and $(1, -1)$ for $-1$. For a bounded operator on
an infinite-dimensional Banach space, the set of eigenvalues, its point spectrum, can be empty while the spectrum is not.

## Statements

- [Eigenvector of a linear map](has-eigenvector.md)
- [Eigenspace of a linear map](eigenspace.md): the eigenvectors for one scalar, together with $0$
- [Eigenvalues of a linear map](eigenvalues.md): the set of eigenvalues, for a bounded operator its point spectrum

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 5.5 (eigenvalue), 5.8 (eigenvector) and 5.52 (eigenspace), the case of operators on real or complex vector spaces (version read: the open-access PDF dated 4 November 2026).
