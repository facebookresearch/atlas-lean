# Existence of eigenvalues

Let $K$ be an algebraically closed field and $V$ a nonzero finite-dimensional vector space over $K$. Then every
$K$-linear map $f \colon V \to V$ has an eigenvalue: there is $c \in K$ whose eigenspace $\ker(f - c \cdot 1)$ is not
zero, that is, $f(v) = c v$ for some nonzero $v \in V$. This is the general form of the theorem that every operator on a
nonzero finite-dimensional complex vector space has an eigenvalue: take $K = \mathbb C$, which is algebraically closed
by the fundamental theorem of algebra.

## Idea

Over $\mathbb C$ this is where the triangular, Jordan and spectral forms of operators start. A proof: for $v \neq 0$ the
$n + 1$ vectors $v, f v, \dots, f^n v$, with $n = \dim V$, are linearly dependent, so $p(f) v = 0$ for some nonzero
polynomial $p$ of degree at most $n$, which is not constant because $v \neq 0$. Over $K$, $p$ is a constant times a
product of factors $X - c_i$; if every $f - c_i$ were injective, so would be $p(f)$, so some $c_i$ is an eigenvalue.
Both hypotheses are needed: the rotation of $\mathbb R^2$ by a right angle has no real eigenvalue, and multiplication by
$x$ on the space of complex polynomials has no eigenvalue.

## Statements

- [Existence of an eigenvalue over an algebraically closed field](exists-eigenvalue.md)

## Background

- [Eigenvalues and eigenvectors](../eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/README.md): eigenvalues and eigenspaces

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 5.19, the case of complex vector spaces (version read: the open-access PDF dated 4 November 2026).
