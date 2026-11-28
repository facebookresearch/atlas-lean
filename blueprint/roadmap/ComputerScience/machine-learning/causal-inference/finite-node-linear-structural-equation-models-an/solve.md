# Solution of linear structural equations

For $n$ nodes, a coefficient matrix $B$, where $B_{ij}$ is the coefficient of $X_j$ in the equation of $X_i$, and a noise vector $e$, the solution vector of the linear structural equations $X = B X + e$ is defined as $(1 - B)^{-1} e$, for any $B$ (with the matrix inverse taken as $0$ when $1 - B$ is singular); the definition does not assert that this vector solves the equations.

When $B$ is strictly lower triangular this is the unique solution ([Recursive linear structural equations have a unique solution](eq-solve-iff.md)).
