# Standard data: product error at most C ε plus ε for 0 ≤ τ ≤ T

Let $k_1 > 0$, $k_{-1}, k_{-2} \ge 0$, $k_2 > 0$, $s_0, p_0 \ge 0$ and $\varepsilon > 0$, and let
$T$ be real. Let $(s, c, e, p)$ be a [solution](is-solution.md) of the reversible Michaelis–Menten
system with the standard data $s(0) = s_0$, $c(0) = 0$, $e(0) = \varepsilon$ and $p(0) = p_0$, and
let $\bar S : \mathbb{R} \to \mathbb{R}$ be differentiable at every $\tau \ge 0$ with
$\bar S'(\tau) = -v(\bar S(\tau), s_0 + p_0 - \bar S(\tau))$ there, for the
[reduced rate](reduced-rate.md) at total mass $s_0 + p_0$, with $\bar S(0) = s_0$. Then for every
$\tau \in [0, T]$, $\tau = 0$ included, the product tracks the reduced product
$\bar P = s_0 + p_0 - \bar S$:

$$|p(\tau/\varepsilon) - (s_0 + p_0 - \bar S(\tau))| \le (C(T) + 1)\, \varepsilon,$$

with the [constant of the substrate estimate](rev-substrate-error-const.md) $C(T)$ at
$M = s_0 + p_0$.
