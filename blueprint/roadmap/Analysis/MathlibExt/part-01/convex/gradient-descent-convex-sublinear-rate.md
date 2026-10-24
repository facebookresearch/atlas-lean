---
article_id: af_beb6ab1c34f0ed92e45f1743
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gradient_descent_convex_sublinear_rate
---

# Gradient Descent

Gradient descent on a smooth convex function in finite dimensions: with a
step below `1 / L`, the objective gap after `k` steps is at most
`‖X 0 - x⋆‖^2 / (2 * η * k)`.

Proof: The descent lemma and first-order convexity inequality are proved on affine lines. They
bound each objective gap by a difference of squared distances to `x⋆`; telescoping and the
monotonicity of `f (X k)` give the rate, as in L. Vandenberghe, ECE236C lecture notes
"Gradient method" (Spring 2022), slides 1.23-1.26.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Convex.GradientDescent](../../../../../sources/v2/MathlibExt.md)
- `Mathlib/docs/undergrad.yaml`, section `Numerical Analysis` / `Iterative methods of solving systems of real and vector-valued equations`, entries `optimization of convex function in finite dimension` and `gradient descent square root` (unmapped); Y. Nesterov, Introductory Lectures on Convex Optimization, Section 2.1; stable ref https://en.wikipedia.org/wiki/Gradient_descent.
