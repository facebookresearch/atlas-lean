# Fraction-free (Bareiss-Jordan) elimination

For an integer matrix $M$, **Bareiss-Jordan elimination** performs Gauss-Jordan elimination in which, after pivoting on entry $(k, k)$ with previous pivot $p_{k-1}$ (and $p_0 = 1$), every other entry is updated by $a_{ij} \leftarrow (a_{kk} a_{ij} - a_{ik} a_{kj}) / p_{k-1}$, with row exchanges to find nonzero pivots. All divisions are exact over $\mathbb{Z}$, and by Sylvester's determinant identity every intermediate entry equals (up to sign) a minor of $M$ of order at most $k + 1$.

## Depends on

- [Existence of the reduced row echelon form](../../../LinearAlgebra/matrix-decompositions/gaussian-elimination-and-row-echelon-form/exists-is-reduced-row-echelon-row-equiva.md)

## Sources

- E. H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination", Mathematics of Computation 22(103), 1968.
- A. Schrijver, "Theory of Linear and Integer Programming", John Wiley & Sons, 1986.
