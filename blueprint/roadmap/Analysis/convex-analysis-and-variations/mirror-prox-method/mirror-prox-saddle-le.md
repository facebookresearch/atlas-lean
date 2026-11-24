# Mirror-prox for convex-concave saddle points

Let $E_x, E_y$ be real normed spaces, $X \subseteq E_x$, $Y \subseteq E_y$, and let $f$ be convex in $x \in X$ for every $y \in Y$ and concave in $y \in Y$ for every $x \in X$. Let $F(x, y)(a, b) = F_x(x, y)(a) - F_y(x, y)(b)$ on $E_x \times E_y$ (with the max norm), where $F_x$ and $F_y$ satisfy the first-order inequalities

$$
f(x', y) \ge f(x, y) + F_x(x, y)(x' - x), \qquad f(x, y') \le f(x, y) + F_y(x, y)(y' - y)
$$

for $(x, y) \in X \times Y$, $x' \in X$, $y' \in Y$ (for differentiable $f$, the partial derivatives, so that $F = (\partial_x f, -\partial_y f)$). Let $F$ be $L$-Lipschitz on $Z = X \times Y$, $\omega$ $\alpha$-strongly convex on $Z$ in the Bregman form, $0 < \gamma$ with $\gamma L \le \alpha$, and let $z_t, w_t \in Z$ satisfy the optimality conditions of the mirror-prox steps. Then for $N \ge 1$ the average $(\bar x_N, \bar y_N) = \frac1N\sum_{t<N} w_t$ satisfies

$$
f(\bar x_N, y) - f(x, \bar y_N) \le \frac{V_{z_0}(x, y)}{\gamma N} \qquad \text{for all } x \in X,\ y \in Y .
$$

The proof bounds $F(w_t)(w_t - (x, y)) \ge f(x_t, y) - f(x, y_t)$ at each leading point $w_t = (x_t, y_t)$, sums with the [telescoped bound](mirror-prox-sum-le.md), and applies Jensen's inequality in each variable.

## Sources

- A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim. 15(1) (2004), 229–251; author PDF at <https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf>, Section 2, Proposition 2.2(ii), the bound on $\epsilon_f$ with $\epsilon_t = 0$, for constant steps and the iteration that always performs both prox steps; the source takes $f$ continuously differentiable on compact $X$ and $Y$.
