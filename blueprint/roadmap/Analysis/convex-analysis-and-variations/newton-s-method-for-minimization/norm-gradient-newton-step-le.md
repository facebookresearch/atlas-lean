# One pure Newton step squares the gradient norm

Let $E$ be a real Hilbert space and let $f \colon E \to \mathbb{R}$ have a gradient $\nabla f$ that is differentiable at every point, with derivative (Hessian) $H(y)$ satisfying $\|H(y) - H(y')\| \le L \|y - y'\|$ for some $L \ge 0$. Let $m > 0$ and suppose $\langle H(x) v, v \rangle \ge m \|v\|^2$ for all $v$. If $\Delta$ solves $H(x) \Delta = -\nabla f(x)$, then

$$\|\nabla f(x + \Delta)\| \le \frac{L}{2m^2} \|\nabla f(x)\|^2.$$

Only the lower Hessian bound at $x$ itself is used.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.5.3, eq. (9.33).
