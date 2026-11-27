# With s₀ > 0 and c₀, e₀ ≥ 0, s tracks a positive reduced solution

Let $k_1 > 0$, $k_b \ge 0$ and $k_2 > 0$, so that the [Michaelis constant](michaelis-constant.md)
$K_M = (k_b + k_2)/k_1$ is positive, and let $(s, c, e, p)$ be a [solution](is-solution.md) of the
Michaelis–Menten mass-action system with initial values $s(0) > 0$, $c(0) \ge 0$ and $e(0) \ge 0$.
Let $\bar S : \mathbb{R} \to \mathbb{R}$ be differentiable at every $\tau \ge 0$ with
$\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$ there, a solution of the reduced
(Michaelis–Menten) equation, with $\bar S(0) > 0$. Write $e_T = e(0) + c(0)$ for the total enzyme,
$s_T = s(0) + c(0)$, and $q(x) = e_T x/(K_M + x)$ for the
[quasi-steady-state complex](qss-complex.md) at total enzyme $e_T$. Then for every $t \ge 0$, with
the reduced solution run on the slow clock $\tau = e_T t$,

$$
|s(t) - \bar S(e_T t)| \le |s(0) - \bar S(0)| + (k_1 s_T + k_b)
\Bigl(\frac{|c(0) - q(s(0))|}{k_b + k_2} + \frac{e_T^2 (k_1 s_T + k_b)}{K_M (k_b + k_2)}\, t\Bigr).
$$
