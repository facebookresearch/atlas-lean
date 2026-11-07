# Entries of the Jacobian matrix are partial derivatives

Let
$f : \mathbb{R}^m \to \mathbb{R}^n$ and $x \in \mathbb{R}^m$. For every row index $i$ and column
index $j$, the $(i, j)$ entry of the Jacobian matrix of $f$ at $x$ is the derivative at $t = 0$
of $t \mapsto f_i(x + t e_j)$, where $f_i$ is the $i$-th component of $f$ and $e_j$ is the
$j$-th standard basis vector of $\mathbb{R}^m$. This derivative is taken to be $0$ when it does
not exist.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `Jacobian matrix` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
