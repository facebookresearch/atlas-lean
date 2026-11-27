# Steepest descent iteration

Let $A$ be a symmetric positive definite $n \times n$ matrix, $b \in \mathbb{R}^n$ and $x_* = A^{-1} b$. The *steepest descent iteration* for $Ax = b$ starts from $x_0$ and, for $k \ge 0$, sets

$$r_k = b - A x_k, \qquad \alpha_k = \frac{r_k^T r_k}{r_k^T A r_k}, \qquad x_{k+1} = x_k + \alpha_k r_k,$$

until $r_k = 0$: once $r_k = 0$, $x_k = x_*$ and the iterates stay at $x_k$. Each step is the orthogonal [projection method](projection-method.md) with $\mathcal{K} = \mathcal{L} = \operatorname{span}\{r_k\}$, so $x_{k+1}$ minimizes $f(x) = \|x - x_*\|_A^2$ on the line $x_k + \mathbb{R} r_k$, along the negative gradient of $f$, and consecutive residuals are orthogonal.

## Depends on

- [Projection method](projection-method.md)
- [Energy norm](../../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/energy-norm.md)

## Proof depends on

- [Galerkin projection minimizes the energy norm of the error](galerkin-projection-minimizes-the-energy-norm-of-the-error.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.3.1, Algorithm 5.2 and the discussion before Lemma 5.8. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
