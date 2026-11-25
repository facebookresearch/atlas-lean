# Convexity is monotonicity of the gradient

Let $s \subseteq \mathbb{R}^n$ be open and convex and $f$ differentiable on $s$. Then $f$ is convex on $s$ if and only if its gradient is monotone: $(\nabla f(x) - \nabla f(y))^{\mathsf T}(x - y) \ge 0$ for all $x, y \in s$.

Proof. If $f$ is convex, adding the first-order inequalities $f(y) \ge f(x) + \nabla f(x)^{\mathsf T}(y - x)$ and $f(x) \ge f(y) + \nabla f(y)^{\mathsf T}(x - y)$ gives monotonicity. Conversely, for $x, y \in s$ put $\varphi(t) = f(x + t(y - x))$ on $[0, 1]$. Then $\varphi'(t) = \nabla f(x + t(y - x))^{\mathsf T}(y - x)$, and for $t < u$ monotonicity at the points $x + t(y - x)$ and $x + u(y - x)$ gives $(u - t)(\varphi'(u) - \varphi'(t)) \ge 0$; so $\varphi'$ is nondecreasing, $\varphi$ is convex, and convexity of $f$ along every segment in $s$ is convexity of $f$ on $s$.

## Proof depends on

- [First-order characterization of convexity](convex-on-iff-forall-add-fderiv-le.md): first-order characterization of convexity.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, Exercise 3.11 (gradients of differentiable convex functions are monotone)
