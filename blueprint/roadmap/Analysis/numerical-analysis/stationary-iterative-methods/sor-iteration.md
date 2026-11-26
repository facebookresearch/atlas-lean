# Successive overrelaxation

Let $A = D - E - F$ be an $n \times n$ real or complex matrix with nonzero diagonal, split as for the [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md), and let $\omega \ne 0$ be a real parameter. The *successive overrelaxation* (SOR) iteration for $Ax = b$ takes a weighted combination of the old value and the Gauss–Seidel update, component by component:

$$x_{k+1, i} = (1 - \omega)\, x_{k, i} + \frac{\omega}{a_{ii}} \Bigl(b_i - \sum_{j < i} a_{ij} x_{k+1, j} - \sum_{j > i} a_{ij} x_{k, j}\Bigr), \qquad i = 1, \dots, n.$$

It is the [splitting iteration](splitting-iteration.md) with $M = \tfrac{1}{\omega}(D - \omega E)$, and its iteration matrix is

$$G_\omega = (D - \omega E)^{-1}\bigl(\omega F + (1 - \omega) D\bigr).$$

For $\omega = 1$ it is the Gauss–Seidel iteration; $\omega > 1$ is overrelaxation and $\omega < 1$ underrelaxation.

## Depends on

- [Splitting iteration](splitting-iteration.md)
- [Jacobi and Gauss–Seidel iterations](jacobi-and-gauss-seidel-iteration-matrices.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.1, the SOR iteration (4.12) and the componentwise form after it, the preconditioner (4.26), and the formula for $M_{SOR}$ before Theorem 4.16. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), the description of SOR as a loop and as a splitting. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
