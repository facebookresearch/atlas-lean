# Karush–Kuhn–Tucker conditions for inequality constraints

Let $E$ be a finite-dimensional
real normed space, let $f \colon E \to \mathbb{R}$ and $g_1, \dots, g_m \colon E \to \mathbb{R}$,
and let $x \in E$ be a point at which $f$ and every $g_i$ are differentiable; write $D$ for
the Fréchet derivative at $x$. Suppose that $x$ is feasible, that is $g_i(x) \le 0$ for every
$i$; that $x$ is a local minimizer of $f$ on the feasible set
$\{y \in E : g_i(y) \le 0 \text{ for every } i\}$; and that the derivatives $Dg_i(x)$ of the
active constraints, those $i$ with $g_i(x) = 0$, are linearly independent. Then there exist
multipliers $\lambda_1, \dots, \lambda_m \ge 0$ such that $\lambda_i g_i(x) = 0$ for every $i$
and $Df(x) + \sum_{i=1}^m \lambda_i Dg_i(x) = 0$.

## Sources

- W. Karush, Minima of Functions of Several Variables with Inequalities as Side Conditions (M.Sc. thesis, Univ. Chicago, 1939); H. W. Kuhn and A. W. Tucker, Nonlinear Programming, Proc. Second Berkeley Symposium (1951), 481–492, DOI 10.1525/9780520411586-036.
