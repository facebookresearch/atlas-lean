# The Stein equation: series solution and uniqueness

Let $M \in \mathbb{C}^{n \times n}$ and $N \in \mathbb{C}^{m \times m}$ be convergent (every eigenvalue of modulus less than $1$), and let $W \in \mathbb{C}^{n \times m}$. Then the Stein equation

$$X = M^\top X N + W$$

has exactly one solution $X \in \mathbb{C}^{n \times m}$, namely

$$X = \sum_{k = 0}^{\infty} (M^\top)^k\, W\, N^k ,$$

and the series converges absolutely. With $M = N = A$ square and $W = -Q$ this is the discrete Lyapunov equation $A^\top P A - P = Q$; for real $A$ that case is the existing page listed under Background. The transpose is not conjugated, so for complex $M$ the series need not be Hermitian or positive semidefinite even when $W$ is.

**Proof.** Because $M^\top$, which has the eigenvalues of $M$, and $N$ are convergent, there are $c \ge 1$ and $0 \le \rho < 1$ with $\|(M^\top)^k\|, \|N^k\| \le c \rho^k$ for all $k$, in a submultiplicative norm. Hence $\|(M^\top)^k W N^k\| \le c^2 \|W\| \rho^{2k}$, and the series converges absolutely. Its sum $X$ satisfies $M^\top X N = \sum_{k \ge 1} (M^\top)^k W N^k = X - W$. If $X_1$ and $X_2$ are two solutions, then $D = X_1 - X_2$ satisfies $D = M^\top D N$, hence $D = (M^\top)^k D N^k$ for every $k$, and $\|D\| \le c^2 \rho^{2k} \|D\| \to 0$. So $D = 0$.

## Proof depends on

- [Exponential stability of linear difference equations](asymptotic-stability-linear-difference-equations.md): powers of a convergent matrix decay geometrically

## Background

- [Discrete Lyapunov equation for convergent matrices](discrete-lyapunov-equation.md): the real case $M = N = A$, $W = -Q$, with definiteness of the solution

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 4.2, Lemma 2.1 (the series $\sum_k F^k A (F^\top)^k$ converges when every eigenvalue of $F$ has modulus less than $1$, p. 64) and the existence and uniqueness argument in the proof of Theorem 2.1 for $P - F P F^\top = Q$ (pp. 64–65).
