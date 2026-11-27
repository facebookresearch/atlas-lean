# Projection method

Let $A$ be an $n \times n$ real matrix, $b \in \mathbb{R}^n$, $x_0 \in \mathbb{R}^n$, and let $\mathcal{K}$ and $\mathcal{L}$ be subspaces of $\mathbb{R}^n$ of the same dimension $m$. A *projection method onto $\mathcal{K}$ orthogonally to $\mathcal{L}$*, with starting vector $x_0$, seeks $\tilde x$ such that

$$\tilde x \in x_0 + \mathcal{K}, \qquad b - A\tilde x \perp \mathcal{L}$$

(the Petrov–Galerkin conditions). It is *orthogonal* when $\mathcal{L} = \mathcal{K}$, and the conditions are then the Galerkin conditions; otherwise it is *oblique*. If $V$ and $W$ are $n \times m$ matrices whose columns are bases of $\mathcal{K}$ and $\mathcal{L}$, then $\tilde x = x_0 + V y$ with $W^T A V\, y = W^T r_0$, $r_0 = b - A x_0$, which determines $\tilde x$ uniquely whenever $W^T A V$ is nonsingular.

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.1, conditions (5.3)–(5.6), the matrix representation (5.7), and the terms orthogonal and oblique projection method. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
