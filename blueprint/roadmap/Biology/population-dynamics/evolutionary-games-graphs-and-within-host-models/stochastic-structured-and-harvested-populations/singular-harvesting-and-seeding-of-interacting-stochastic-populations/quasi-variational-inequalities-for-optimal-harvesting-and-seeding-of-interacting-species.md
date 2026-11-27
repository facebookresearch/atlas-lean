# Quasi-variational inequalities for optimal harvesting and seeding of interacting species

**Setting.** $d$ interacting species with densities $\xi(t) \in [0,\infty)^d$ follow $d\xi = b(\xi)\,dt + \sigma(\xi)\,dw$ with $b(0) = \sigma(0) = 0$ and generator $\mathcal L\Phi = b\cdot\nabla\Phi + \frac12\operatorname{tr}(\sigma\sigma^\top\nabla^2\Phi)$. A harvesting–seeding strategy consists of nondecreasing càdlàg processes $Y(t)$ (cumulative harvest) and $Z(t)$ (cumulative seeding), possibly singular, giving

$$X(t) = x + \int_0^t b(X(s))\,ds + \int_0^t \sigma(X(s))\,dw(s) - Y(t) + Z(t).$$

With discount rate $\delta > 0$, marginal harvest prices $f_i$ and seeding costs $g_i$, the value function is

$$V(x) = \sup_{(Y,Z)} \mathbb E_x\Big[\int_0^\infty e^{-\delta s}\big(f(X(s^-))\cdot dY(s) - g(X(s^-))\cdot dZ(s)\big)\Big].$$

Standing assumption (Assumption 3.2): $b, \sigma$ continuous with unique global uncontrolled solutions, and $f_i, g_i$ continuous, non-increasing, with $f_i(x) < g_i(y)$ for all $x, y$ (seeding always costs more than harvesting pays).

**Theorem.**
1. (Proposition 3.4) For all $x, y$, $V(y) \le V(x) - f(x)\cdot(x-y)^+ + g(x)\cdot(x-y)^-$; if $V(0) < \infty$, then $V$ is finite everywhere and Lipschitz.
2. (Proposition 3.6) If $b_i(x) \le \delta x_i + C$ for all $i$, then $V(x) \le \sum_i f_i(0)x_i + M$ for a constant $M$.
3. (Theorem 3.8) If $V < \infty$, it is a viscosity solution of the HJB quasi-variational inequality

$$\max_i\Big\{(\mathcal L - \delta)V(x),\ f_i(x) - \frac{\partial V}{\partial x_i}(x),\ \frac{\partial V}{\partial x_i}(x) - g_i(x)\Big\} = 0.$$

4. (Theorem 3.10, verification) If a nonnegative $\Phi \in C^2$ satisfies the inequality with $\le 0$ everywhere, then $V \le \Phi$; if moreover $(\mathcal L - \delta)\Phi = 0$ on the non-intervention region $\mathcal C = \{f_i < \partial_i\Phi < g_i\}$ and a strategy keeps $X$ in $\overline{\mathcal C}$, harvesting only where $\partial_i\Phi = f_i$ and seeding only where $\partial_i\Phi = g_i$, then $\Phi = V$ and that strategy is optimal.
5. (Theorem 3.14) The value functions $V^h$ of locally consistent controlled Markov-chain approximations with step $h$ converge to the value function $V^U$ of the problem in which admissible strategies keep the state in a bounded box $[0,U]^d$, so near-optimal chain strategies are near-optimal for that problem (and for the original one when $V = V^U$).

## Expansion

The gradient constraints come from instantaneous actions: harvesting a small amount $\varepsilon$ of species $i$ earns $f_i\varepsilon$ and lowers the state, so optimality requires $\partial_iV \ge f_i$; seeding costs $g_i\varepsilon$, so $\partial_iV \le g_i$. Inside the non-intervention region the population evolves freely and the value satisfies the discounted Dynkin equation $(\mathcal L - \delta)V = 0$. Optimal strategies are therefore of reflection type at free boundaries, with harvesting when populations are abundant and seeding when a species is close to extinction. Seeding can be worthwhile even though it costs more than the harvest price, because it prevents the loss of all future harvests at extinction.

## Sources

- Alexandru Hening, Ky Quan Tran, Tien Trong Phan and George Yin, "Harvesting of interacting stochastic populations", arXiv:1810.05609 (2018), Section 3 (model, Assumption 3.2, Propositions 3.4 and 3.6, Theorems 3.8, 3.10 and 3.14), <https://doi.org/10.48550/arXiv.1810.05609>. Published version: Journal of Mathematical Biology, Vol. 79, Issue 2, 533-570, 2019.
