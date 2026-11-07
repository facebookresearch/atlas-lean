# Velocities of curves in a level set lie in the kernel of the derivative

Let $E$ be a
real normed space, $c \in \mathbb{R}$, and $f : E \to \mathbb{R}$ a function differentiable at
$x \in E$. If a curve $\gamma : \mathbb{R} \to E$ satisfies $\gamma(0) = x$, has derivative $v$ at
$0$, and satisfies $f(\gamma(t)) = c$ for all $t \in \mathbb{R}$, then $Df(x)v = 0$.

Proof: Apply the chain rule to `f ∘ γ`, then compare its derivative with that of the constant
function determined by the level-set equation.

## Sources

- `Mathlib/docs/undergrad.yaml`, section `Multivariable calculus` / `Submanifolds of R^n`, entry `tangent space` (unmapped); J. M. Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 5.12; stable ref https://en.wikipedia.org/wiki/Tangent_space.
