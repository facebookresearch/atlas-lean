# Minimal residual projection minimizes the residual

Let $A$ be an $n \times n$ real matrix and $\mathcal{K}$ a subspace with $\ker A \cap \mathcal{K} = \{0\}$ (as for nonsingular $A$), and let $\mathcal{L} = A\mathcal{K}$, which then has the dimension of $\mathcal{K}$. A vector $\tilde x$ is the result of the [projection method](projection-method.md) onto $\mathcal{K}$ orthogonally to $\mathcal{L}$ with starting vector $x_0$ if and only if it minimizes the Euclidean norm of the residual over $x_0 + \mathcal{K}$:

$$\|b - A\tilde x\|_2 = \min_{x \in x_0 + \mathcal{K}} \|b - Ax\|_2 .$$

The minimizer is then unique. Without the condition on $\ker A$ the least-squares problem still has minimizers, characterized by $b - A\tilde x \perp A\mathcal{K}$, but $A\mathcal{K}$ has smaller dimension and the projection method as defined does not apply; for $A = 0$ every $x \in x_0 + \mathcal{K}$ minimizes. The method is oblique in general, but orthogonal when $A\mathcal{K} = \mathcal{K}$, for instance for $A = I$.

## Depends on

- [Projection method](projection-method.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.2.1, Proposition 5.3 and its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
