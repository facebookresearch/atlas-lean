# Convergence of stationary iterations

Let $G$ be an $n \times n$ complex matrix. If its spectral radius satisfies $\rho(G) < 1$, then $I - G$ is nonsingular and, for every vector $f$ and every starting vector $x_0$, the iteration $x_{k+1} = G x_k + f$ converges to the unique solution $x^*$ of $x = Gx + f$, with error $x_k - x^* = G^k (x_0 - x^*)$. Conversely, if the iteration converges for every $f$ and every $x_0$, then $\rho(G) < 1$.

In particular a [splitting iteration](splitting-iteration.md) for $Ax = b$ converges from every starting vector, for every $b$, exactly when its iteration matrix $M^{-1}N$ has spectral radius less than $1$. Since $\rho(G) \le \|G\|$ for every operator norm, $\|G\| < 1$ in some operator norm suffices.

## Depends on

- [Splitting iteration](splitting-iteration.md)

## Proof depends on

- [Powers of a matrix tend to zero exactly when its spectral radius is less than one](matrix-powers-tend-to-zero.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.1, Theorem 4.1 and Corollary 4.2. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
- J. W. Demmel, Math 221 (Applied Numerical Linear Algebra), University of California, Berkeley, Fall 2024, typed notes of Lecture 12 (Splitting Methods, 12 November 2024), the theorem that $x_{i+1} = Rx_i + c$ converges for all $x_0$ if and only if $\rho(R) < 1$, with the two lemmas before it. <https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_12.txt>
