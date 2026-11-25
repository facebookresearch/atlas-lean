# For prepared data the rate-law error bound holds from τ = 0

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, with $K_M = (k_b + k_2)/k_1$ the
[Michaelis constant](michaelis-constant.md), and let $\bar S : \mathbb{R} \to \mathbb{R}$ be
differentiable at every $\tau \ge 0$ with $\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$
there, a solution of the reduced (Michaelis–Menten) equation, with $\bar S(0) = s_0$. Let
$\varepsilon > 0$ and $T$ be real, and let $(s, c, e, p)$ be a [solution](is-solution.md) of the
Michaelis–Menten mass-action system with prepared data: $s(0) = s_0$, total enzyme
$e(0) + c(0) = \varepsilon$, and the complex on the quasi-steady-state manifold,
$c(0) = \varepsilon s_0/(K_M + s_0)$, the [quasi-steady-state complex](qss-complex.md). Then for
every $\tau \in [0, T]$, $\tau = 0$ included, with $v(x) = k_2 x/(K_M + x)$, the
[Michaelis–Menten rate law](mm-rate.md) with $V_{\max} = k_2$,

$$\Bigl|\frac{k_2 c(\tau/\varepsilon)}{\varepsilon} - v(\bar S(\tau))\Bigr| \le P(\varepsilon),$$

the [prepared-data bound](prepared-rate-bound.md) for these $s_0$ and $T$: there is no initial
layer.
