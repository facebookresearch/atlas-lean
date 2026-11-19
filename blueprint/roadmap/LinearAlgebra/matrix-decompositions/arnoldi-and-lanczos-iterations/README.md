# Arnoldi and Lanczos iterations

The Arnoldi iteration is Gram–Schmidt orthonormalization of the Krylov sequence $r, Tr, T^2r, \dots$ (Trefethen and Bau, Lecture 33). The coefficients $h_{ij} = \langle q_i, Tq_j\rangle$ form an upper Hessenberg matrix and satisfy the Arnoldi relation $TQ_n = Q_{n+1}\tilde H_n$; for symmetric $T$ the matrix is tridiagonal and the iteration is the three-term Lanczos recurrence (Lecture 36). Statements are in exact arithmetic and assume no breakdown (linearly independent Krylov vectors).

- [Krylov vectors](krylov-vec.md)
- [Arnoldi vectors](arnoldi-vec.md)
- [Arnoldi Hessenberg matrix](hessenberg.md)
- [Arnoldi vectors are orthonormal](orthonormal-arnoldi-vec.md)
- [Arnoldi vectors span the Krylov spaces](span-arnoldi-vec-iic.md)
- [Orthonormal expansion in a finite span](eq-sum-inner-smul-of-mem-span.md)
- [An orthonormal vector is orthogonal to the span of the others](inner-eq-zero-of-mem-span.md)
- [The operator maps each Arnoldi vector into the next Krylov space](map-arnoldi-vec-mem-span.md)
- [The Arnoldi matrix is upper Hessenberg](hessenberg-eq-zero.md)
- [The Arnoldi matrix is an upper Hessenberg matrix](is-upper-hessenberg-hessenberg.md)
- [The Arnoldi relation](arnoldi-relation.md)
- [Lanczos: for symmetric operators the Arnoldi matrix is tridiagonal](hessenberg-eq-zero-of-is-symmetric.md)

## Related topics

- [GMRES](../gmres/README.md)
- [Conjugate gradient method](../conjugate-gradient-method/README.md)
- [QR factorization](../qr-factorization/README.md)
