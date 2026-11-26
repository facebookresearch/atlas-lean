# Linear convergence of gradient descent for strongly convex functions

Let $E$ be a real Hilbert space, let $m, L > 0$, and let $f \colon E \to \mathbb{R}$ be differentiable and $m$-strongly convex with $L$-Lipschitz gradient. Let $0 < \eta \le 1/L$ and let $x_{k+1} = x_k - \eta \nabla f(x_k)$ for all $k \ge 0$. Then for every $x^\star \in E$ (in particular a minimizer) and every $k \ge 0$,

$$f(x_k) - f(x^\star) \le (1 - \eta m)^k \big(f(x_0) - f(x^\star)\big),$$

where $0 \le 1 - \eta m < 1$ when $E \ne 0$. With $\eta = 1/L$ the contraction factor is $c = 1 - m/L$.

Proof: each step decreases $f$ by at least $\frac{\eta}{2}\|\nabla f(x_k)\|^2$, and strong convexity gives $\|\nabla f(x_k)\|^2 \ge 2m\big(f(x_k) - f(x^\star)\big)$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.3.1, eq. (9.18) (there with $c = 1 - m/M$ for exact line search).
- Cf. Y. Nesterov, *Introductory Lectures on Convex Optimization: A Basic Course*, Kluwer, 2004, Ch. 2 (the gradient method on smooth strongly convex functions).
