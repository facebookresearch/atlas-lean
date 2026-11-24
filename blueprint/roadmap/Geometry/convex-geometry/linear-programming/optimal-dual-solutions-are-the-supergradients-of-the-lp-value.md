# Optimal dual solutions are the supergradients of the LP value function

Let $V(b) = \sup\{c^{\mathsf T}x : Ax \le b, x \ge 0\} \in [-\infty, \infty]$ for a real $m \times n$ matrix $A$ and $c \in \mathbb{R}^n$, and let $V(b)$ be finite. A vector $y \in \mathbb{R}^m$ is an optimal solution of the dual problem $\min\{b^{\mathsf T}y : A^{\mathsf T}y \ge c, y \ge 0\}$ exactly when it is a supergradient of $V$ at $b$: $V(b') \le V(b) + y^{\mathsf T}(b' - b)$ for every $b'$. Consequently, if $b$ is an interior point of the set where $V$ is finite and the optimal dual solution $y$ is unique, then $V$ is differentiable at $b$ with $\nabla V(b) = y$.

Proof of the reverse inclusion. Let $y$ be a supergradient. For $b' = b + e_i$, $V(b') \ge V(b)$ gives $y_i \ge 0$. For $x \ge 0$, $c^{\mathsf T}x \le V(Ax) \le V(b) + y^{\mathsf T}(Ax - b)$, so $(c - A^{\mathsf T}y)^{\mathsf T}x \le V(b) - b^{\mathsf T}y$ for every $x \ge 0$; scaling $x$ forces $A^{\mathsf T}y \ge c$, and $x = 0$ gives $b^{\mathsf T}y \le V(b)$. By weak duality every dual feasible $y'$ has $b^{\mathsf T}y' \ge V(b)$, so $y$ is dual optimal. The forward inclusion is the supporting-price inequality.

## Proof depends on

- [Optimal dual solutions are supergradients of the LP value function](lp-value-supporting-price-inequality.md): optimal dual solutions are supergradients.
- [Weak duality](../../../Analysis/convex-analysis-and-variations/lagrange-duality/dual-value-le-primal-value.md): weak duality.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- A concave function that is finite near an interior point and has exactly one supergradient there is differentiable at that point.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, Section 5.6.2, A global inequality, eq. (5.57), <https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, Section 5.6.3, Local sensitivity analysis, eq. (5.58), <https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
