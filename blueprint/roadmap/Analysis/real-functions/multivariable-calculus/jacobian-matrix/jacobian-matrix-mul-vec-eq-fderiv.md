# The Jacobian matrix computes the derivative

Let $f : \mathbb{R}^m \to \mathbb{R}^n$ be
differentiable at $x \in \mathbb{R}^m$, and let $J$ be the Jacobian matrix of $f$ at $x$. Then for
every $v \in \mathbb{R}^m$, the product $J v$ equals $Df(x)\, v$, the Fréchet derivative of $f$ at
$x$ applied to $v$.

Proof: The Jacobian is the matrix of the Fréchet derivative (Wikipedia, "Jacobian matrix and
determinant": it represents the total derivative), and multiplying a vector by the matrix of a
linear map applies the map to that vector.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `Jacobian matrix` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
