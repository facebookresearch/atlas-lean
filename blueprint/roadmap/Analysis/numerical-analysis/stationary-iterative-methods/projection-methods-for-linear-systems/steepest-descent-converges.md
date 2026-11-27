# Convergence of steepest descent

Let $A$ be a symmetric positive definite matrix with extreme eigenvalues $\lambda_{\min}$ and $\lambda_{\max}$, and let $x_k$ be the iterates of the [steepest descent iteration](steepest-descent-iteration.md) for $Ax = b$, with errors $d_k = x_* - x_k$. Then

$$\|d_{k+1}\|_A \le \frac{\lambda_{\max} - \lambda_{\min}}{\lambda_{\max} + \lambda_{\min}}\, \|d_k\|_A ,$$

so the iteration converges from every starting vector, with factor $(\kappa - 1)/(\kappa + 1)$ where $\kappa = \lambda_{\max}/\lambda_{\min}$.

## Depends on

- [Steepest descent iteration](steepest-descent-iteration.md)
- [Spectral condition number of a positive definite matrix](../../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/cond-num.md)

## Proof depends on

- [Kantorovich inequality](../../../inequalities/kantorovich-bhatia-davis-and-popoviciu-inequalit/kantorovich-inequality.md)
- [Galerkin projection minimizes the energy norm of the error](galerkin-projection-minimizes-the-energy-norm-of-the-error.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.3.1, Lemma 5.8 (Kantorovich inequality) and Theorem 5.9 with its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
