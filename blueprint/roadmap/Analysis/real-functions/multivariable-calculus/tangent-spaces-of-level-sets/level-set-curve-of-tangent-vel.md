# Kernel vectors are velocities of curves in a regular level set

Let $E$ be a real
Banach space, $f : E \to \mathbb{R}$ a $C^1$ function, $c \in \mathbb{R}$, and $x \in E$ a point
with $f(x) = c$ at which the derivative $Df(x) : E \to \mathbb{R}$ is surjective. Then for every
$v \in E$ with $Df(x)v = 0$ there is a curve $\gamma : \mathbb{R} \to E$ with $\gamma(0) = x$,
$\gamma'(0) = v$ and $f(\gamma(t)) = c$ for all $t \in \mathbb{R}$.

Proof: Use the implicit function theorem to construct a local curve tangent to the kernel vector,
then compose it with a bounded arctangent reparametrization to obtain a curve on all of `ℝ`
(implicit function theorem, Banach space version:
https://en.wikipedia.org/wiki/Implicit_function_theorem).

## Sources

- J. M. Lee, Introduction to Smooth Manifolds, 2nd ed., Theorem 5.12.
