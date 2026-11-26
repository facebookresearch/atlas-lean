# Jacobi and Gauss–Seidel iterations

Let $A$ be an $n \times n$ real or complex matrix with nonzero diagonal entries, and write $A = D - E - F$, where $D$ is the diagonal of $A$ and $-E$ and $-F$ are its strictly lower and strictly upper triangular parts. For $Ax = b$:

- the *Jacobi iteration* solves the $i$-th equation for $x_i$ with the other unknowns at their previous values, $x_{k+1, i} = \bigl(b_i - \sum_{j \ne i} a_{ij} x_{k, j}\bigr)/a_{ii}$; it is the [splitting iteration](splitting-iteration.md) with $M = D$, and its iteration matrix is $G_J = I - D^{-1} A = D^{-1}(E + F)$;
- the *Gauss–Seidel iteration* uses the components already updated in the same sweep, $x_{k+1, i} = \bigl(b_i - \sum_{j < i} a_{ij} x_{k+1, j} - \sum_{j > i} a_{ij} x_{k, j}\bigr)/a_{ii}$ for $i = 1, \dots, n$ in order; it is the splitting iteration with $M = D - E$, and its iteration matrix is $G_{GS} = I - (D - E)^{-1} A = (D - E)^{-1} F$.

Unlike the Jacobi iteration, the Gauss–Seidel iteration depends on the order of the unknowns.

## Depends on

- [Splitting iteration](splitting-iteration.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.1, equations (4.2)–(4.8) and (4.19)–(4.25). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), the descriptions of Jacobi and Gauss–Seidel as loops and as splittings. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
