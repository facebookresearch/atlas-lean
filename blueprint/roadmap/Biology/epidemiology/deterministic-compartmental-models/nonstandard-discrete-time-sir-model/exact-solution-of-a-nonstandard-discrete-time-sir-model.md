# Exact solution and long-term behaviour of a nonstandard discrete-time SIR model

**Model.** The continuous SIR model with standard incidence, $\dot x = -\frac{bxy}{x+y}$, $\dot y = \frac{bxy}{x+y} - cy$, $\dot z = cy$, with transmission rate $b > 0$, removal rate $c > 0$ and basic reproduction number $\mathcal{R}_0 = b/c$, is discretized with step $h > 0$ by the Mickens-type nonstandard finite difference scheme

$$\frac{x_{n+1} - x_n}{h} = -\frac{b\,x_{n+1}y_n}{x_n + y_n}, \qquad \frac{y_{n+1} - y_n}{h} = \frac{b\,x_{n+1}y_n}{x_n + y_n} - c\,y_{n+1}, \qquad \frac{z_{n+1} - z_n}{h} = c\,y_{n+1},$$

with $x_0, y_0 > 0$, $z_0 \ge 0$ and $N = x_0 + y_0 + z_0$. Solving for the new values gives an explicit recursion.

**Theorem.**
1. *Dynamical consistency.* For every $h > 0$ the solution stays nonnegative and $x_n + y_n + z_n = N$ for all $n$.
2. *Exact solution.* With $\bar\kappa = x_0/y_0$ and $\xi = \dfrac{1 + ch}{1 + bh}$,

$$x_n = x_0\prod_{i=1}^n \frac{1 + \bar\kappa\,\xi^{i-1}}{1 + bh + \bar\kappa\,\xi^{i-1}}, \qquad y_n = \frac{y_0}{\xi^n}\prod_{i=1}^n \frac{1 + \bar\kappa\,\xi^{i-1}}{1 + bh + \bar\kappa\,\xi^{i-1}}, \qquad z_n = N - x_n - y_n.$$

3. *Long-term behaviour.* If $\mathcal{R}_0 \ge 1$, every solution converges to $(0, 0, N)$. If $\mathcal{R}_0 < 1$, every solution converges to $(\alpha, 0, N - \alpha)$ for some $\alpha \in (0, N]$.

## Proof sketch

The scheme is implicit only linearly: $x_{n+1} = x_n\frac{x_n + y_n}{x_n + y_n + bh\,y_n}$, then $y_{n+1}$ and $z_{n+1}$ follow, so positivity and conservation hold for any step size, unlike forward Euler. The ratio $\kappa_n = x_n/y_n$ satisfies the linear recursion $\kappa_{n+1} = \xi\,\kappa_n$, so $\kappa_n = \bar\kappa\,\xi^n$; substituting into the update for $x$ gives the product formula, verified by induction. When $b \ge c$ we have $\xi \le 1$ and each factor is bounded away from $1$, so $x_n \to 0$. When $b < c$, $\xi > 1$, the factors tend to $1$ geometrically, the product converges to a positive limit and some susceptibles escape.

## Sources

- Márcia Lemos-Silva, Sandra Vaz and Delfim F.M. Torres, "Exact solution for a discrete-time SIR model", *Applied Numerical Mathematics* 207 (2025), 339–347, <https://doi.org/10.1016/j.apnum.2024.09.014>. Preprint version: arXiv:2409.09157 (2024), Section 3: Proposition 2 (nonnegativity and conservation), Theorem 1 (exact solution), Theorems 2 and 3 (long-term behaviour), <https://doi.org/10.48550/arXiv.2409.09157>.
