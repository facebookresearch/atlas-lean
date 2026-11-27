# Galerkin projection minimizes the energy norm of the error

Let $A$ be a symmetric positive definite $n \times n$ matrix, let $x_*$ solve $Ax = b$, and let $\mathcal{K}$ be a subspace. A vector $\tilde x$ is the result of the orthogonal [projection method](projection-method.md) onto $\mathcal{K}$ with starting vector $x_0$ if and only if it minimizes the $A$-norm of the error over $x_0 + \mathcal{K}$:

$$\tilde x \in x_0 + \mathcal{K}, \qquad \|x_* - \tilde x\|_A = \min_{x \in x_0 + \mathcal{K}} \|x_* - x\|_A, \qquad \|y\|_A = (y^T A y)^{1/2} .$$

## Depends on

- [Projection method](projection-method.md)
- [Energy norm](../../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/energy-norm.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.2.1, Proposition 5.2 and its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
