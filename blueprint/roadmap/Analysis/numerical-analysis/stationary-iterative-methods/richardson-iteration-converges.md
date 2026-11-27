# Convergence of Richardson's iteration

Let $A$ be a real $n \times n$ matrix whose eigenvalues are all real, with smallest eigenvalue $\lambda_{\min}$ and largest $\lambda_{\max}$, and for $\alpha > 0$ consider Richardson's iteration

$$x_{k+1} = x_k + \alpha (b - A x_k),$$

the [splitting iteration](splitting-iteration.md) with iteration matrix $G_\alpha = I - \alpha A$. If $\lambda_{\min} > 0$, the iteration converges for every right-hand side and every starting vector exactly when $0 < \alpha < 2/\lambda_{\max}$; then $\rho(G_\alpha) = \max\{|1 - \alpha\lambda_{\min}|, |1 - \alpha\lambda_{\max}|\}$, which is smallest for $\alpha_{\mathrm{opt}} = 2/(\lambda_{\min} + \lambda_{\max})$, where

$$\rho(G_{\alpha_{\mathrm{opt}}}) = \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}} .$$

If $\lambda_{\min} < 0 < \lambda_{\max}$, then $\rho(G_\alpha) > 1$ for every $\alpha$.

## Depends on

- [Splitting iteration](splitting-iteration.md)

## Proof depends on

- [Convergence of stationary iterations](convergence-of-stationary-iterations.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 4.2.1, Example 4.1, equations (4.31)–(4.32), and the computation of $\alpha_{\mathrm{opt}}$ and $\rho_{\mathrm{opt}}$ that follows it. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
