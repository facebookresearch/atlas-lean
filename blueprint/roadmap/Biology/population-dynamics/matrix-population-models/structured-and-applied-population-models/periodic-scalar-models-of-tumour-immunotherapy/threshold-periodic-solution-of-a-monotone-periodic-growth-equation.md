# Threshold periodic solution of a monotone periodic growth equation

Consider $\dot x = x\,F(t,x)$, $x(t_0) = x_0 \ge 0$, where $F : [0,\infty)^2 \to \mathbb R$ satisfies
- (A1) $F$ is continuous and locally Lipschitz in $x$;
- (A2) $F(t+1, x) = F(t, x)$ (period $1$);
- (A3) $F$ is strictly increasing in $x$;
- (A4) $F$ is uniformly bounded.

Solutions exist globally, are unique, and stay positive when $x_0 > 0$. Let $F_A = \int_0^1 F(s, 0)\,ds$.

**Theorem 1.** If $F_A > 0$, every solution with $x_0 > 0$ tends to $+\infty$.

**Theorem 2.** If $F_A < 0$ and $F(t,x) \to f(t) > 0$ uniformly as $x \to \infty$, there is a curve $\gamma : [0,1) \to (0,\infty)$ such that solutions with $x_0 < \gamma(t_0)$ converge to $0$, solutions with $x_0 > \gamma(t_0)$ diverge to $+\infty$, and the solution with $x_0 = \gamma(t_0)$ is the unique positive periodic solution, whose graph separates the two basins.

**Lemma (linear periodic forcing).** For $\dot x = F(t) - G(t)x$, $x(0) = 0$, with $1$-periodic $F$ and $G > 0$, $G_A = \int_0^1 G$, every solution converges to the $1$-periodic function

$$x^*(t) = \frac{K}{1 - e^{-G_A}}\,e^{-\int_0^{\{t\}} G} + \int_0^{\{t\}} F(s)\,e^{-\int_s^{\{t\}} G}\,ds, \qquad K = \int_0^1 F(s)\,e^{-\int_s^1 G}\,ds,$$

where $\{t\} = t - \lfloor t \rfloor$.

**Application (prostate cancer vaccination).** In a seven-equation model of vaccine uptake by dendritic cells, regulatory and cytotoxic T cells and tumour cells, periodic vaccination makes every immune variable asymptotically $1$-periodic (by the lemma), and the scaled tumour size obeys

$$\dot x = x\left(g - \frac{H(t)}{1 + x}\right),$$

with tumour growth rate $g$ and periodic immune killing $H(t)$. If $g > H_A := \int_0^1 H$ the tumour grows without bound from any positive size; if $g < H_A$ there is a periodic threshold $x^*(t_0)$ below which treatment cures and above which it fails.

## Expansion

Integrating over one period gives $x(t+n+1) = x(t+n)\exp\int_{t+n}^{t+n+1} F(s, x(s))\,ds$, and monotonicity bounds the exponent below by $F_A$, so $x$ grows geometrically when $F_A > 0$. When $F_A < 0$, uniqueness means trajectories cannot cross, so the sign of $x(t_0 + 1) - x_0$ is preserved along the orbit and decides between monotone convergence to $0$ and divergence of the period-map iterates. Small data decay because $F(\cdot, x) \approx F(\cdot, 0)$ has negative mean, large data grow because $F \to f > 0$, and continuous dependence gives a unique intermediate fixed point of the period map. If $F$ does not depend on $t$, the result reduces to the familiar unstable equilibrium separating extinction and escape. For the tumour equation, $F(t, 0) = g - H(t)$ and $F \to g > 0$, so the mean killing rate $H_A$ is the cure threshold.

## Sources

- U. Foryś, M. Bodnar, Y. Kogan, "Asymptotic dynamics of some t-periodic one-dimensional model with application to prostate cancer immunotherapy", Journal of Mathematical Biology (2016), Eq. (1) with assumptions (A1)–(A4), Theorems 1–2, Remark 2, Eqs. (2) and (7)–(9), Lemma 1 and Theorem 3, <https://doi.org/10.1007/s00285-016-0978-4>, PMCID PMC5018042.
