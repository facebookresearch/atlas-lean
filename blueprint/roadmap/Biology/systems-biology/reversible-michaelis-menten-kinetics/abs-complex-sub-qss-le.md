# Nonnegative data: past an initial layer, c nears the QSS manifold

Let $k_1, k_{-1}, k_{-2} \ge 0$ and $k_2 > 0$, and let $(s, c, e, p)$ be a
[solution](is-solution.md) of the reversible Michaelis–Menten system with
$s(0), c(0), e(0), p(0) \ge 0$. Write $e_T = e(0) + c(0)$, $M = s(0) + c(0) + p(0)$, $q$ for the
[quasi-steady-state complex](rev-qsscomplex.md) with total enzyme $e_T$, and $F$ for the
[forcing constant](complex-forcing-const.md) at $M$. Then for every $t \ge 0$

$$
|c(t) - q(s(t), p(t))| \le |c(0) - q(s(0), p(0))|\, e^{-(k_{-1} + k_2) t} +
\frac{e_T^2 F}{(k_{-1} + k_2)^2}.
$$

The first term is an initial layer, decaying at the rate $k_{-1} + k_2$; the second is of order $e_T^2$.
