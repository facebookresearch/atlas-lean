# Second-order characterization of convexity

Let $E$ be a real normed space, let $s \subseteq E$ be open, and let $f \colon E \to \mathbb{R}$ have, at every point $y \in s$, a Fréchet derivative $Df(y)$ and a second derivative $D^2 f(y)$ (the derivative of $Df$ at $y$), so that $D^2 f(y)(v, v)$ is the Hessian quadratic form $v^{\mathsf T} \nabla^2 f(y)\, v$. If $s$ is convex, then $f$ is convex on $s$ if and only if $D^2 f(y)(v, v) \ge 0$ for all $y \in s$ and $v \in E$, i.e. $\nabla^2 f(y) \succeq 0$ on $s$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §3.1.4 (proof left as exercise 3.8).
