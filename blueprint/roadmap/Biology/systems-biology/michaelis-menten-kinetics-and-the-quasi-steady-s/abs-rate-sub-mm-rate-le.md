# Slow-clock rate-law error for s₀ > 0, c₀, e₀ ≥ 0 and e₀ + c₀ > 0

Let $k_1 > 0$, $k_b \ge 0$ and $k_2 > 0$, so that the [Michaelis constant](michaelis-constant.md)
$K_M = (k_b + k_2)/k_1$ is positive, and let $(s, c, e, p)$ be a [solution](is-solution.md) of the
Michaelis–Menten mass-action system with initial values $s(0) > 0$, $c(0) \ge 0$ and $e(0) \ge 0$.
Assume moreover that the total enzyme $e_T = e(0) + c(0)$ is positive, and let
$\bar S : \mathbb{R} \to \mathbb{R}$ be differentiable at every $\tau \ge 0$ with
$\bar S'(\tau) = -k_2 \bar S(\tau)/(K_M + \bar S(\tau))$ there, a solution of the reduced
(Michaelis–Menten) equation, with $\bar S(0) > 0$. Write $s_T = s(0) + c(0)$ and
$q(x) = e_T x/(K_M + x)$ for the [quasi-steady-state complex](qss-complex.md). Then for every slow
time $\tau \ge 0$, with $v(x) = k_2 x/(K_M + x)$, the [Michaelis–Menten rate law](mm-rate.md) with
$V_{\max} = k_2$,

$$
\begin{aligned}
\Bigl|\frac{k_2 c(\tau/e_T)}{e_T} - v(\bar S(\tau))\Bigr| \le k_2 \Bigl(
&\frac{|c(0) - q(s(0))|}{e_T}\, e^{-(k_b + k_2)\tau/e_T} \\
&+ \frac{e_T (k_1 s_T + k_b)}{K_M (k_b + k_2)} + \frac{|s(\tau/e_T) - \bar S(\tau)|}{K_M}\Bigr):
\end{aligned}
$$

the slow-time product rate $dP/d\tau = k_2 c(\tau/e_T)/e_T$ differs from the Michaelis–Menten rate
by at most an initial-layer term, a slaving term and the substrate error divided by $K_M$.
