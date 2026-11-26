# Ostrowski–Reich theorem

Let $A$ be a real symmetric $n \times n$ matrix with positive diagonal entries, and let $0 < \omega < 2$. Then the [SOR iteration](sor-iteration.md) with parameter $\omega$ converges for every starting vector $x_0$ (and every right-hand side) if and only if $A$ is positive definite.

In particular, for a symmetric positive definite matrix the Gauss–Seidel iteration ($\omega = 1$) always converges. For such matrices the range $0 < \omega < 2$ is also necessary: SOR converges for every right-hand side and every starting vector if and only if $0 < \omega < 2$.

## Depends on

- [Successive overrelaxation](sor-iteration.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.4, Theorem 4.10 and the paragraph before it. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), Theorem 3 (for symmetric positive definite $A$, SOR($\omega$) converges if and only if $0 < \omega < 2$), referring for the proof to J. W. Demmel, *Applied Numerical Linear Algebra*, SIAM, 1997, Theorem 6.5. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
