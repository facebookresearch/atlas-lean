# Rate-law error bound for standard data on a slow window

For real $k_1, k_b, k_2, s_0, T, \tau_0$ and $\varepsilon$, the rate-law error bound is

$$
B(\varepsilon) = k_2 \Bigl(e^{-(k_b + k_2)\tau_0/\varepsilon} + \varepsilon \Bigl(
\frac{k_1 s_0 + k_b}{K_M (k_b + k_2)} + \frac{C(T)}{K_M}\Bigr)\Bigr),
$$

with the [Michaelis constant](michaelis-constant.md) $K_M = (k_b + k_2)/k_1$, the
[constant of the substrate estimate](substrate-error-const.md) $C(T)$ and quotients by $0$ read as
$0$; at $\varepsilon = 0$ the exponent is $0$ and $B(0) = k_2$. When $K_M = 0$, which happens
exactly when $k_1 = 0$ or $k_b + k_2 = 0$, both quotients by $K_M$ are $0$ and
$B(\varepsilon) = k_2 e^{-(k_b + k_2)\tau_0/\varepsilon}$. The exponential is the initial-layer
term: for $k_b + k_2 > 0$ and $\varepsilon > 0$ it is small exactly when
$(k_b + k_2)\tau_0/\varepsilon$ is large. In the model $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$, $s_0 > 0$,
$\tau_0 \ge 0$ and $\varepsilon > 0$, where $K_M > 0$ and $k_b + k_2 > 0$.
