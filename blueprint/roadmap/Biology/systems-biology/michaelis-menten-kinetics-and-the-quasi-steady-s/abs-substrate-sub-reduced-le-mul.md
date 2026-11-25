# Standard data: slow-time substrate error at most C ε for 0 ≤ τ ≤ T

Let $k_1 > 0$, $k_b \ge 0$, $k_2 > 0$ and $s_0 > 0$, with $K_M = (k_b + k_2)/k_1$ the
[Michaelis constant](michaelis-constant.md), and let $\bar S : \mathbb{R} \to \mathbb{R}$ be
differentiable at every $\tau \ge 0$ with $\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$
there, a solution of the reduced (Michaelis–Menten) equation, with $\bar S(0) = s_0$. Let
$\varepsilon > 0$ and $T$ be real, and let $(s, c, e, p)$ be a [solution](is-solution.md) of the
Michaelis–Menten mass-action system with the standard data $s(0) = s_0$, $c(0) = 0$ and
$e(0) = \varepsilon$. Then for every slow time $\tau \in [0, T]$, $\tau = 0$ included,

$$|s(\tau/\varepsilon) - \bar S(\tau)| \le C(T)\, \varepsilon,$$

with the [constant of the substrate estimate](substrate-error-const.md) $C(T)$: the substrate has no
initial layer. For $T < 0$ the window is empty.
