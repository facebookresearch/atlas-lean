# Singular values

Let $E$ and $F$ be finite-dimensional inner product spaces over $\mathbb K = \mathbb R$ or $\mathbb C$, with
$n = \dim E$, and let $T \colon E \to F$ be a linear map with adjoint $T^*$. The singular values of $T$ form the
sequence $\sigma_0 \geq \sigma_1 \geq \cdots$ in which $\sigma_0, \dots, \sigma_{n-1}$ are the square roots of the
eigenvalues of the operator $T^* T$ on $E$, in decreasing order and each repeated as many times as the dimension of its
eigenspace, and $\sigma_i = 0$ for $i \geq n$.

## Idea

The eigenvalues of $T^* T$ are nonnegative, since $\langle T^* T x, x\rangle = \lVert T x\rVert^2$, so their square
roots are real. Singular values measure how much $T$ stretches: $\sigma_0$ is the operator norm of $T$, exactly
$\operatorname{rank} T$ of them are positive, and for real spaces $T$ maps the closed unit ball of $E$ onto a solid
ellipsoid in its range whose semi-axes have the positive singular values as lengths. For example $T(x, y) = (2x, 0)$ on
$\mathbb R^2$ has $T^* T (x, y) = (4x, 0)$, so $\sigma_0 = 2$ and $\sigma_1 = 0$. Conventions differ on how many
values to list: this sequence keeps the $n$ values for $E$ and pads with zeros, while some books list only the positive
ones. The singular value decomposition writes $T$ in orthonormal bases as a diagonal matrix with these entries.

## Statements

- [Singular values of a linear map](singular-values.md)

## Background

- [Eigenvalues and eigenvectors](../../eigenvalues-and-canonical-forms/eigenvalues-and-eigenspaces/eigenvalues-and-eigenvectors/README.md): the eigenvalues of $T^* T$

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 7.65 (version read: the open-access PDF dated 4 November 2026).
