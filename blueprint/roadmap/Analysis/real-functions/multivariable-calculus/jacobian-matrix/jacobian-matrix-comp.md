# Chain rule for Jacobian matrices

Let $f : \mathbb{R}^m \to \mathbb{R}^n$,
$g : \mathbb{R}^n \to \mathbb{R}^p$ and $x \in \mathbb{R}^m$, and write $J_h(y)$ for the Jacobian
matrix of $h$ at $y$. If $f$ is differentiable at $x$ and $g$ is differentiable at $f(x)$, then
$J_{g \circ f}(x) = J_g(f(x))\, J_f(x)$, a product of a $p \times n$ and an $n \times m$ matrix.

Proof: As in Wikipedia, "Jacobian matrix and determinant" (chain rule), write each Jacobian as
the matrix of the Fréchet derivative, then use the chain rule for Fréchet derivatives and the
fact that the matrix of a composition of linear maps is the product of their matrices.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.15.
