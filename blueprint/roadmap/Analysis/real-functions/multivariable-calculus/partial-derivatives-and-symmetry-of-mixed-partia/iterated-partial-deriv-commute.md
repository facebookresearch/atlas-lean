# Symmetry of mixed partial derivatives (Clairaut's theorem)

For a function
$g : \mathbb{R}^n \to \mathbb{R}$, write $\partial_i g$ for its partial derivative along the
$i$-th coordinate axis. If $f : \mathbb{R}^n \to \mathbb{R}$ is twice continuously
differentiable, then for all coordinate indices $i, j$ and every point $x \in \mathbb{R}^n$,
$\partial_j (\partial_i f)(x) = \partial_i (\partial_j f)(x)$.

The proof writes both mixed partials as values of the second Fréchet derivative of $f$ at $x$
and applies Schwarz's theorem on the symmetry of second derivatives.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Differential calculus`, entry `k-th order partial derivatives` (unmapped); W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).
