# Optimality criterion for convex problems

Let $E$ be a real normed space, let $s \subseteq E$, and let $f \colon E \to \mathbb{R}$ be convex on $s$ (so $s$ is convex) and Fréchet differentiable at $a \in s$. Then $a$ minimizes $f$ over $s$ if and only if

$$Df(a)(x - a) \ge 0 \quad \text{for every } x \in s.$$

Geometrically, when $Df(a) \ne 0$ it defines a supporting hyperplane to the feasible set at $a$.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004 (https://web.stanford.edu/~boyd/cvxbook/), §4.2.3, eq. (4.21).
