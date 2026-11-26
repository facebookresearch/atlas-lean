# Minimal residual projection minimizes the residual

Let $A$ be an $n \times n$ real matrix and $\mathcal{K}$ a subspace, and let $\mathcal{L} = A\mathcal{K}$. A vector $\tilde x$ is the result of the oblique [projection method](projection-method.md) onto $\mathcal{K}$ orthogonally to $\mathcal{L}$ with starting vector $x_0$ if and only if it minimizes the Euclidean norm of the residual over $x_0 + \mathcal{K}$:

$$\|b - A\tilde x\|_2 = \min_{x \in x_0 + \mathcal{K}} \|b - Ax\|_2 .$$

## Depends on

- [Projection method](projection-method.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.2.1, Proposition 5.3 and its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
