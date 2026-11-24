# On the QSS manifold the rescaled substrate rate is the reduced field

Let $k_1 > 0$, $k_2 \ne 0$, $s_0 \ne 0$ and $e_0 \ne 0$, let $k_b$ and $u$ be real with
$K_M + s_0 u \ne 0$, where $K_M = (k_b + k_2)/k_1$ is the
[Michaelis constant](../michaelis-constant.md), and let $q = e_0 s_0 u/(K_M + s_0 u)$ be the
[quasi-steady-state complex](../qss-complex.md) at the substrate $s_0 u$. Then the
[substrate rate](../substrate-rate.md) at substrate $s_0 u$, complex $q$ and free enzyme $e_0 - q$,
rescaled to $u = s/s_0$ and slow time $\theta = t/t_S$, is the [reduced field](reduced-field.md):

$$
\frac{t_S}{s_0} \bigl(-k_1 (e_0 - q)\, s_0 u + k_b q\bigr) =
-\frac{(1 + \kappa)\, u}{\kappa + u},
$$

with the [slow time scale](slow-time-scale.md) $t_S = (s_0 + K_M)/(k_2 e_0)$ and $\kappa = K_M/s_0$.
This eliminates $c$ by setting $c' = 0$; it is not a statement about solutions, which is the
[QSSA contract](qssacontract.md).
