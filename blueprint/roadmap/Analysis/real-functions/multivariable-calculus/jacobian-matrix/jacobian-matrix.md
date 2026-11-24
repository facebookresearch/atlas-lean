# Jacobian matrix

For $f : \mathbb{R}^m \to \mathbb{R}^n$ and $x \in \mathbb{R}^m$, the
Jacobian matrix of $f$ at $x$ is the $n \times m$ real matrix whose $(i, j)$ entry is the partial
derivative of the $i$-th component $f_i$ of $f$ in the $j$-th coordinate direction at $x$: the
derivative at $t = 0$ of $t \mapsto f_i(x + t e_j)$, where $e_j$ is the $j$-th standard basis
vector of $\mathbb{R}^m$. A partial derivative that does not exist is taken to be $0$.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9; stable ref https://en.wikipedia.org/wiki/Jacobian_matrix_and_determinant.
