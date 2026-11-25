# Strong duality under Slater's condition with affine equality constraints

Let $f_0, \dots, f_m : \mathbb{R}^n \to (-\infty, \infty]$ be convex, $D = \bigcap_{i=0}^m \operatorname{dom} f_i$, $A$ a real $p \times n$ matrix and $b \in \mathbb{R}^p$, and consider minimizing $f_0(x)$ subject to $f_i(x) \le 0$ for $i = 1, \dots, m$ and $Ax = b$, with optimal value $p^\star$. Let $g(\lambda, \nu) = \inf_{x \in D}\big(f_0(x) + \sum_i \lambda_i f_i(x) + \nu^{\mathsf T}(Ax - b)\big)$ and $d^\star = \sup_{\lambda \ge 0, \nu} g(\lambda, \nu)$. If some $x$ in the relative interior of $D$ has $f_i(x) < 0$ for every $i$ and $Ax = b$ (Slater's condition), then $d^\star = p^\star$, and when $d^\star > -\infty$ some $(\lambda^\star, \nu^\star)$ with $\lambda^\star \ge 0$ has $g(\lambda^\star, \nu^\star) = d^\star$. Inequality constraints whose $f_i$ is affine need only $f_i(x) \le 0$ at the Slater point.

## Background

- [Strong duality under Slater's condition](dual-value-eq-primal-value-of-slater.md): the case without equality constraints.
- [Weak duality](dual-value-le-primal-value.md): weak duality.

## Sources

- S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004, <https://web.stanford.edu/~boyd/cvxbook/>, §5.2.3, problem (5.25) and conditions (5.26)–(5.27)
