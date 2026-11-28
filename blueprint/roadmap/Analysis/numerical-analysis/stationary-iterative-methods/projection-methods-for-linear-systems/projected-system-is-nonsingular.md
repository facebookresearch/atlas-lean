# The projected system is nonsingular in the two standard cases

Let $A$ be an $n \times n$ real matrix and $\mathcal{K}$, $\mathcal{L}$ subspaces of $\mathbb{R}^n$ of dimension $m$, with bases forming the columns of $V$ and $W$. If either

1. $A$ is positive definite ($x^T A x > 0$ for $x \ne 0$) and $\mathcal{L} = \mathcal{K}$, or
2. $A$ is nonsingular and $\mathcal{L} = A\mathcal{K}$,

then $W^T A V$ is nonsingular, for every choice of the bases, so the [projection method](projection-method.md) onto $\mathcal{K}$ orthogonally to $\mathcal{L}$ is well defined.

## Depends on

- [Projection method](projection-method.md)

## Sources

- Y. Saad, *Iterative Methods for Sparse Linear Systems*, 2nd edition, SIAM, 2003, Section 5.1, Proposition 5.1 and its proof. <https://www-users.cse.umn.edu/~saad/IterMethBook_2ndEd.pdf>
