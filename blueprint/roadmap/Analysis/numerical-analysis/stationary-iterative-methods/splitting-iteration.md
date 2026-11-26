# Splitting iteration

Let $A$ be an $n \times n$ real or complex matrix and $b$ a vector. A *splitting* of $A$ is a decomposition $A = M - N$ with $M$ nonsingular. The associated *splitting iteration* (stationary iteration, or relaxation scheme) for $Ax = b$ is

$$x_{k+1} = M^{-1} N x_k + M^{-1} b, \qquad k = 0, 1, 2, \dots,$$

from a starting vector $x_0$. It has the form $x_{k+1} = G x_k + f$ with *iteration matrix* $G = M^{-1} N = I - M^{-1} A$ and $f = M^{-1} b$. A limit $x$ of the iterates satisfies $x = Gx + f$, that is $Mx = Nx + b$, so $Ax = b$; the iteration is a fixed-point iteration for the preconditioned system $M^{-1} A x = M^{-1} b$.

Writing $A = D - E - F$, with $D$ the diagonal of $A$, assumed nonsingular, and $-E$ and $-F$ its strictly lower and strictly upper triangular parts, the Jacobi iteration takes $M = D$, the Gauss–Seidel iteration $M = D - E$ and successive overrelaxation $M = D/\omega - E$ for a real $\omega \ne 0$.

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.1.2, equations (4.18)–(4.25), and Section 4.2, equation (4.28) and the paragraph after (4.29). <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), the definition of a splitting and of the iteration (*). <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
