# Convergence of the Jacobi method for strictly diagonally dominant matrices

Let $A$ be a
real square matrix with rows and columns indexed by a finite type, and let $b$ be a real vector.
Suppose $A$ is strictly diagonally dominant: $\sum_{j \ne i} |A_{ij}| < |A_{ii}|$ for every $i$.
Define the Jacobi sweep $J$ by $J(x)_i = \bigl(b_i - \sum_{j \ne i} A_{ij} x_j\bigr) / A_{ii}$.
Then there is a vector $x^*$ with $A x^* = b$ such that, for every starting vector $x_0$, the
iterates $J^k(x_0)$ converge to $x^*$ as $k \to \infty$.

## Sources

- Mathlib repository, `docs/undergrad.yaml` (the undergraduate curriculum list), section "Numerical Analysis" / "Iterative methods" / "Jacobian"; G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins Univ. Press, 2013, §11.2; https://en.wikipedia.org/wiki/Jacobi_method
