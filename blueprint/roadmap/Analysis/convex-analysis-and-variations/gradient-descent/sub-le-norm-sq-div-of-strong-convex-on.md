# Suboptimality bound from strong convexity

Let $E$ be a real Hilbert space, let $m > 0$, and let $f \colon E \to \mathbb{R}$ be $m$-strongly convex on $E$ with gradient $g$ at $x$. Then for every $y \in E$,

$$f(x) - f(y) \le \frac{\|g\|^2}{2m};$$

in particular $f(x) - p^\star \le \|\nabla f(x)\|^2 / (2m)$, so a small gradient certifies near-optimality.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §9.1.2, eq. (9.9).
