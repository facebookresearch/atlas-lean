# Partial derivative as the derivative of a coordinate slice

For
$f : \mathbb{R}^n \to \mathbb{R}$, a coordinate index $i$ and a point $x \in \mathbb{R}^n$, let
$e_i$ be the $i$-th standard basis vector. The partial derivative of $f$ along the $i$-th
coordinate axis at $x$ equals the derivative at $t = 0$ of the one-variable function
$t \mapsto f(x + t e_i)$, taken to be $0$ when that function is not differentiable at $0$.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `partial derivatives` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Ch. 9.
