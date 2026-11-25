# Rate-law error bound for prepared data

For real $k_1, k_b, k_2, s_0, T$ and $\varepsilon$, the rate-law error bound for prepared data is

$$
P(\varepsilon) = k_2 \varepsilon\, \frac{k_1 (s_0 + \varepsilon) + k_b}{K_M (k_b + k_2)}
\Bigl(1 + \frac{(k_1 (s_0 + \varepsilon) + k_b)\, T}{K_M}\Bigr),
$$

with the [Michaelis constant](michaelis-constant.md) $K_M = (k_b + k_2)/k_1$ and quotients by $0$
read as $0$. When $K_M = 0$, which happens exactly when $k_1 = 0$ or $k_b + k_2 = 0$, the factor
$(k_1 (s_0 + \varepsilon) + k_b)/(K_M (k_b + k_2))$ is $0$ and $P(\varepsilon) = 0$. In the model
$k_1 > 0$, $k_b \ge 0$, $k_2 > 0$, $s_0 > 0$ and $\varepsilon > 0$, where $K_M > 0$ and
$k_b + k_2 > 0$.
