# Standard data: rate-law error bound on the slow window from τ₀ ≥ 0

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, with $K_M = (k_b + k_2)/k_1$ the
[Michaelis constant](michaelis-constant.md), and let $\bar S : \mathbb{R} \to \mathbb{R}$ be
differentiable at every $\tau \ge 0$ with $\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$
there, a solution of the reduced (Michaelis–Menten) equation, with $\bar S(0) = s_0$. Let
$\varepsilon > 0$, $\tau_0 \ge 0$ and $T$ be real, and let $(s, c, e, p)$ be a
[solution](is-solution.md) of the Michaelis–Menten mass-action system with the standard data
$s(0) = s_0$, $c(0) = 0$ and $e(0) = \varepsilon$. Then for every $\tau \in [\tau_0, T]$, with
$v(x) = k_2 x/(K_M + x)$, the [Michaelis–Menten rate law](mm-rate.md) with $V_{\max} = k_2$,

$$\Bigl|\frac{k_2 c(\tau/\varepsilon)}{\varepsilon} - v(\bar S(\tau))\Bigr| \le B(\varepsilon),$$

the [rate-law error bound](rate-error-bound.md) for these $s_0$, $T$ and $\tau_0$. For $\tau_0 > 0$
it [tends to $0$](tendsto-rate-error-bound.md) as $\varepsilon \to 0^+$; for $\tau_0 = 0$ its
initial-layer term $k_2 e^{-(k_b + k_2)\tau_0/\varepsilon}$ equals $k_2$ for every
$\varepsilon > 0$.
