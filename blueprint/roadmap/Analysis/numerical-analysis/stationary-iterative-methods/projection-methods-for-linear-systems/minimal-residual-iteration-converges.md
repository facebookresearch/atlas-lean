# Convergence of the minimal residual iteration

Let $A$ be a real $n \times n$ matrix that is positive definite, in the sense that its symmetric part $(A + A^T)/2$ is positive definite, let $\mu = \lambda_{\min}((A + A^T)/2)$ and $\sigma = \|A\|_2$. The *minimal residual iteration* sets $r_k = b - A x_k$ and, while $r_k \ne 0$, $\alpha_k = (A r_k)^T r_k / \|A r_k\|_2^2$ and $x_{k+1} = x_k + \alpha_k r_k$, the [projection method](projection-method.md) with $\mathcal{K} = \operatorname{span}\{r_k\}$ and $\mathcal{L} = A\mathcal{K}$; once $r_k = 0$, $x_k$ solves the system and the iterates stay at $x_k$. Its residuals satisfy

$$\|r_{k+1}\|_2 \le \Big(1 - \frac{\mu^2}{\sigma^2}\Big)^{1/2} \|r_k\|_2 ,$$

so the iteration converges from every starting vector.

## Depends on

- [Projection method](projection-method.md)

## Proof depends on

- [Minimal residual projection minimizes the residual](minimal-residual-projection-minimizes-the-residual.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.3.2, Algorithm 5.3 and Theorem 5.10 with its proof, using (5.19), $(Ax, x)/(x, x) \ge \mu$. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
