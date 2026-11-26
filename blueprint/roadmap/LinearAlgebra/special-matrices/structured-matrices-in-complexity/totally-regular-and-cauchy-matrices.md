# Totally regular matrices and Cauchy matrices

A matrix over a field is *totally regular* if all of its square submatrices are nonsingular. For distinct $a_1,\dots,a_m$ and distinct $b_1,\dots,b_n$ with $a_i\neq b_j$, the *Cauchy matrix* $\bigl(1/(a_i-b_j)\bigr)$ is totally regular, since every square submatrix is again Cauchy and $\det\bigl(1/(a_i-b_j)\bigr)=\prod_{i<k}(a_k-a_i)(b_i-b_k)\big/\prod_{i,j}(a_i-b_j)\neq0$. Over a field of characteristic zero the matrix $(1/(i-(N+j)))_{i,j<N}$ is an explicit example.

## Depends on

- [Leibniz formula for the determinant](../../determinants-and-matrix-identities/determinants-of-matrices/leibniz-formula/det-apply.md)

## Sources

- Satyanarayana V. Lokam, "Complexity Lower Bounds using Linear Algebra", Foundations and Trends in Theoretical Computer Science, 2009.
- Joel Friedman, "A note on matrix rigidity", Combinatorica, 1993.
