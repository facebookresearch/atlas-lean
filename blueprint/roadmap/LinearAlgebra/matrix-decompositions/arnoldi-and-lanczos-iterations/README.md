# Arnoldi and Lanczos iterations

Let $T$ be a linear operator on a real or complex inner product space and $r$ a vector such that the Krylov vectors $r, Tr, \dots, T^{k-1} r$ are linearly independent. Let $q_0, \dots, q_{k-1}$ be the Arnoldi vectors, obtained by Gram–Schmidt orthonormalization of the Krylov vectors, and $h_{ij} = \langle q_i, T q_j \rangle$. Then for every $j$ with $j + 1 < k$, $T q_j = \sum_{i=0}^{k-1} h_{ij}\, q_i$.

## Idea

The Arnoldi iteration builds an orthonormal basis of the Krylov spaces $\operatorname{span}\{r, Tr, \dots, T^j r\}$ one vector at a time. Because $T$ maps the $j$-th Krylov space into the next one, $T q_j$ has components only along $q_0, \dots, q_{j+1}$, so the matrix of $T$ compressed to the Krylov space is upper Hessenberg: zero below the first subdiagonal. Hence only the terms with $i \le j + 1$ survive in the sum above; with $n = k - 1$, $Q_n = [q_0 \mid \dots \mid q_{n-1}]$ and $\tilde H_n = (h_{ij})_{0 \le i \le n,\ 0 \le j < n}$, this is the matrix relation $T Q_n = Q_{n+1} \tilde H_n$. The tall matrix $\tilde H_n$ has the square compression $H_n = Q_n^* T Q_n = (h_{ij})_{i, j < n}$ as its top $n \times n$ block, plus one more row whose only possibly nonzero entry is $h_{n, n-1}$. When $T$ is symmetric (self-adjoint), $H_n$ is Hermitian, hence tridiagonal, and the iteration becomes the three-term Lanczos recurrence. The eigenvalues of $H_n$, the Ritz values, approximate eigenvalues of $T$, and the same relation underlies GMRES and the conjugate gradient method. All statements are in exact arithmetic and assume that the Krylov vectors are independent.

## Statements

- [The Arnoldi relation](arnoldi-relation.md)
- [Krylov vectors](krylov-vec.md): the Krylov vectors
- [Arnoldi vectors](arnoldi-vec.md): the Arnoldi vectors
- [Arnoldi Hessenberg matrix](hessenberg.md): the Hessenberg matrix $(h_{ij})$
- [Arnoldi vectors are orthonormal](orthonormal-arnoldi-vec.md): the Arnoldi vectors are orthonormal
- [Arnoldi vectors span the Krylov spaces](span-arnoldi-vec-iic.md): they span the Krylov spaces
- [The operator maps each Arnoldi vector into the next Krylov space](map-arnoldi-vec-mem-span.md): $T q_j$ lies in the next Krylov space
- [The Arnoldi matrix is upper Hessenberg](hessenberg-eq-zero.md): the entries below the subdiagonal vanish
- [The Arnoldi matrix is an upper Hessenberg matrix](is-upper-hessenberg-hessenberg.md): the same, as an upper Hessenberg matrix
- [Lanczos: for symmetric operators the Arnoldi matrix is tridiagonal](hessenberg-eq-zero-of-is-symmetric.md): special case: for symmetric $T$ the matrix is tridiagonal (Lanczos)
- [Orthonormal expansion in a finite span](eq-sum-inner-smul-of-mem-span.md): a lemma on orthonormal expansions
- [An orthonormal vector is orthogonal to the span of the others](inner-eq-zero-of-mem-span.md): a lemma on orthogonality to a span

## Background

- [QR factorization](../qr-factorization/README.md): the Arnoldi vectors are the Gram–Schmidt orthonormalization of the Krylov vectors, that is, the $Q$ factor of the Krylov matrix.

## Related topics

- [GMRES iterate](../gmres/is-gmresiterate.md): an application: GMRES minimizes the residual over the Krylov spaces that the Arnoldi vectors span.
- [The conjugate gradient error bound in terms of the condition number](../conjugate-gradient-method/energy-norm-iterate-sub-le-cond-num.md): for symmetric positive definite systems, the conjugate gradient method works in the Krylov spaces that the Lanczos recurrence generates.
