# Quadratic convergence of the pure Newton method

Let $E$ be a real Hilbert space and let $f \colon E \to \mathbb{R}$ have a differentiable gradient with $L$-Lipschitz Hessian $H$ ($L \ge 0$) satisfying $\langle H(x_k) v, v \rangle \ge m \|v\|^2$ at every iterate $x_k$ and for all $v$, with $m > 0$ (Boyd–Vandenberghe assume $\nabla^2 f \succeq mI$ on the whole sublevel set). If $H(x_k)(x_{k+1} - x_k) = -\nabla f(x_k)$ for every $k$ (pure Newton steps), then with $c = L/(2m^2)$,

$$c\, \|\nabla f(x_k)\| \le \big(c\, \|\nabla f(x_0)\|\big)^{2^k} \quad \text{for all } k.$$

In particular, if $c\, \|\nabla f(x_0)\| \le 1/2$ then $c\, \|\nabla f(x_k)\| \le (1/2)^{2^k}$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.5.3, eq. (9.34) and the recursion after it.
