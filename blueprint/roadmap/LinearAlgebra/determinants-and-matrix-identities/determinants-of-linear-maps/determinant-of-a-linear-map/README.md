# Determinant of a linear map

Let $R$ be a commutative ring and $M$ a module over $R$. The determinant of $R$-linear maps from $M$ to itself is the
multiplicative map $f \mapsto \det f$, with $\det(\mathrm{id}) = 1$, that sends $f$ to the determinant of its matrix in a
basis of $M$ indexed by a finite set of elements of $M$, chosen once and for all, and to $1$ when $M$ has no such basis.
This is the general form of the determinant of a linear operator $T$ on a finite-dimensional vector space $V$ over a
field $F$: with $R = F$ and $M = V$, which has a finite basis, $\det T$ is the determinant of the matrix of $T$ in a basis
of $V$.

## Idea

The determinant does not depend on the basis used to compute it: the matrices $A$ and $A'$ of $T$ in two bases satisfy
$A' = P^{-1} A P$ for an invertible matrix $P$, and $\det(P^{-1} A P) = \det(P)^{-1} \det A \det P = \det A$. So the
determinant belongs to $T$ itself, like its trace and its eigenvalues. It is multiplicative,
$\det(S \circ T) = \det S \det T$; for $V$ finite-dimensional over a field, $T$ is invertible exactly when
$\det T \neq 0$; over $\mathbb C$, $\det T$ is the product of the eigenvalues of $T$, each repeated as many times as its
multiplicity; and on $\mathbb R^n$, $|\det T|$ is the factor by which $T$ multiplies volumes. Some books define the
determinant of an operator through alternating forms instead, as the number $\det T$ such that
$\alpha(Tv_1, \dots, Tv_n) = \det T \cdot \alpha(v_1, \dots, v_n)$ for every alternating $n$-linear form $\alpha$ on $V$,
where $n = \dim V$; it is again the determinant of the matrix of $T$ in any basis.

## Statements

- [Determinant of a linear map](det.md)
- [The determinant of a linear map is the determinant of its matrix in any basis](det-to-matrix.md): basis independence: the basis chosen in the definition may be replaced by any basis indexed by a finite set

## Sources

- S. Axler, *Linear Algebra Done Right*, 4th ed., 9.41 (the definition through alternating forms) and 9.53 (the determinant of the matrix in any basis), the case of operators on nonzero finite-dimensional real or complex vector spaces (version read: the open-access PDF dated 4 November 2026).
