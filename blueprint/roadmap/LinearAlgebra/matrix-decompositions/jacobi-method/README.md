# Convergence of the Jacobi method

Let $A$ be a real square matrix that is strictly diagonally dominant, $\sum_{j \ne i} |A_{ij}| < |A_{ii}|$ for every $i$, and let $b$ be a real vector. Define the Jacobi sweep $J$ by $J(x)_i = \bigl(b_i - \sum_{j \ne i} A_{ij} x_j\bigr)/A_{ii}$. Then there is a vector $x^*$ with $Ax^* = b$ such that, for every starting vector $x_0$, the iterates $J^k(x_0)$ converge to $x^*$.

## Idea

The Jacobi method solves $Ax = b$ by solving the $i$-th equation for $x_i$ while freezing the other unknowns at their previous values, all coordinates at once. Writing $A = D + R$ with $D$ diagonal, the sweep is $x \mapsto D^{-1}(b - Rx)$, an affine map whose linear part $-D^{-1}R$ has maximum-norm operator norm equal to the largest row ratio $\sum_{j \ne i} |A_{ij}|/|A_{ii}|$. Strict diagonal dominance makes this less than $1$, so the sweep is a contraction and the Banach fixed-point theorem gives convergence to the unique solution, at a geometric rate. Diagonally dominant systems arise from discretized differential equations.

## Statements

- [Convergence of the Jacobi method for strictly diagonally dominant matrices](jacobi-iteration-converges.md)
