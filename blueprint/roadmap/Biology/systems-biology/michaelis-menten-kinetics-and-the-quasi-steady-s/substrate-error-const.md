# Constant of the slow-window substrate estimate

For real $k_1, k_b, k_2, s_0$ and $T$, the constant of the substrate estimate on the slow window
$[0, T]$ is

$$
C(T) = (k_1 s_0 + k_b) \Bigl(\frac{1}{k_b + k_2} +
\frac{(k_1 s_0 + k_b)\, T}{K_M (k_b + k_2)}\Bigr),
$$

with the [Michaelis constant](michaelis-constant.md) $K_M = (k_b + k_2)/k_1$ and quotients by $0$
read as $0$. When $K_M = 0$, which happens exactly when $k_1 = 0$ or $k_b + k_2 = 0$, the term in
$T$ vanishes and $C(T) = (k_1 s_0 + k_b)/(k_b + k_2)$, which is $0$ when $k_b + k_2 = 0$. It is
affine in $T$; for $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$ it is positive at $T = 0$ and
increases linearly with $T$.
