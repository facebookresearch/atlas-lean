# Weyl's inequality for singular values

For linear maps $T, U : E \to F$ between finite-dimensional inner product spaces and every $k \ge 0$,
$|\sigma_k(T) - \sigma_k(U)| \le \|T - U\|_2$, where $\sigma_0 \ge \sigma_1 \ge \cdots$ are the singular
values, indexed from $0$ and followed by zeros ($\sigma_k = 0$ for $k \ge \dim E$), and $\|\cdot\|_2$ is the
spectral norm.

## Idea

Singular values are perfectly conditioned: a perturbation of spectral norm $\varepsilon$ moves each of
them by at most $\varepsilon$, for every matrix, normal or not, whereas the eigenvalues of a non-normal
matrix can move much more. The upper half, $\sigma_k(T + U) \le \sigma_k(T) + \|U\|_2$, is trivial for
$k \ge \dim E$, where both singular values are $0$. For $k < \dim E$ it follows from the min–max
description of $\sigma_k(T)$ as the least, over subspaces of codimension $k$, of the norm of $T$ restricted
to the subspace, since adding $U$ changes each such norm by at most $\|U\|_2$; equivalently, $\sigma_k(T)$
is the distance in spectral norm from $T$ to the maps of rank at most $k$. Applying it in both directions
gives the inequality.

## Statements

- [Weyl's inequality for singular values](abs-singular-values-sub-le.md)
- [Upper half of Weyl's inequality for singular values](singular-values-add-le.md): the upper half, used in the proof

## Background

- [Singular values](../../singular-values/README.md): the sequence $\sigma_0 \ge \sigma_1 \ge \cdots$, followed by zeros, that the inequality is about
