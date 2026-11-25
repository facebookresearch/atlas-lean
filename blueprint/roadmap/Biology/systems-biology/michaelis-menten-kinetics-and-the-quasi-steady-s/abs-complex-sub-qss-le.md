# For s₀ > 0, c₀, e₀ ≥ 0, c nears the QSS manifold past an initial layer

Let $k_1 > 0$, $k_b \ge 0$ and $k_2 > 0$, so that the [Michaelis constant](michaelis-constant.md)
$K_M = (k_b + k_2)/k_1$ is positive, and let $(s, c, e, p)$ be a [solution](is-solution.md) of the
Michaelis–Menten mass-action system with initial values $s(0) > 0$, $c(0) \ge 0$ and $e(0) \ge 0$.
Write $e_T = e(0) + c(0)$ for the total enzyme, $s_T = s(0) + c(0)$, and $q(x) = e_T x/(K_M + x)$
for the [quasi-steady-state complex](qss-complex.md) at total enzyme $e_T$. Then for every $t \ge 0$

$$
|c(t) - q(s(t))| \le |c(0) - q(s(0))|\, e^{-(k_b + k_2) t} +
\frac{e_T^2 (k_1 s_T + k_b)}{K_M (k_b + k_2)}.
$$

The first term is an initial layer, decaying at the rate $k_b + k_2 = k_1 K_M$; the second is of
order $e_T^2$.
