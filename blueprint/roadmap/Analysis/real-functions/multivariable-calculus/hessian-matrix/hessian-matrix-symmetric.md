# Symmetry of the Hessian

If $f : \mathbb{R}^n \to \mathbb{R}$ is twice continuously
differentiable, then for every $x \in \mathbb{R}^n$ the Hessian matrix of $f$ at $x$ is symmetric:
it equals its transpose.

Proof: Rewrite the matrix entries as evaluations of the second Fréchet derivative and apply
Schwarz's theorem on the symmetry of second derivatives, as proved in Mathlib, following
Wikipedia's “Symmetry of second derivatives”.

## Sources

- W. Rudin, Principles of Mathematical Analysis, 3rd ed., Theorem 9.41 (pp. 235–236).
