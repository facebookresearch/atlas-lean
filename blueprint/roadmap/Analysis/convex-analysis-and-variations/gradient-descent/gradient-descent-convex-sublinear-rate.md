# Sublinear rate of gradient descent for smooth convex functions

Let $E$ be a
finite-dimensional real inner product space, let $L > 0$, and let $f : E \to \mathbb{R}$ be
convex and differentiable with $L$-Lipschitz gradient $\nabla f$. Let $x^\star \in E$ be a global
minimizer of $f$, let $0 < \eta \le 1/L$, and let $(x_k)_{k \ge 0}$ be any sequence in $E$ with
$x_{k+1} = x_k - \eta \nabla f(x_k)$ for all $k$. Then for every $k \ge 1$,
$f(x_k) - f(x^\star) \le \|x_0 - x^\star\|^2 / (2 \eta k)$.

Proof: The descent lemma and first-order convexity inequality are proved on affine lines. They
bound each objective gap by a difference of squared distances to $x^\star$; telescoping and the
monotonicity of $f(x_k)$ in $k$ give the rate, as in L. Vandenberghe, ECE236C lecture notes
"Gradient method" (Spring 2022), slides 1.23-1.26.

## Sources

- Y. Nesterov, Introductory Lectures on Convex Optimization, Section 2.1; https://en.wikipedia.org/wiki/Gradient_descent.
