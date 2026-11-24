# Nonnegative data: the reversible substrate tracks a reduced solution

Let $k_1 > 0$, $k_{-1}, k_{-2} \ge 0$ and $k_2 > 0$, and let $(s, c, e, p)$ be a
[solution](is-solution.md) of the reversible Michaelis–Menten system with
$s(0), c(0), e(0), p(0) \ge 0$. Write $e_T = e(0) + c(0)$, $M = s(0) + c(0) + p(0)$, $q$ for the
[quasi-steady-state complex](rev-qsscomplex.md) with total enzyme $e_T$, and $F$ for the
[forcing constant](complex-forcing-const.md) at $M$. Let $\bar S : \mathbb{R} \to \mathbb{R}$ be
differentiable at every $\tau \ge 0$ with $\bar S'(\tau) = -v(\bar S(\tau), M - \bar S(\tau))$
there, for the [reduced rate](reduced-rate.md), with $0 \le \bar S(0) \le M$. Then for every
$t \ge 0$, with the reduced solution run on the slow clock $\tau = e_T t$,

$$
\begin{aligned}
|s(t) - \bar S(e_T t)| \le |s(0) - \bar S(0)| + (k_1 M + k_{-1}) \Bigl(
&\frac{|c(0) - q(s(0), p(0))|}{k_{-1} + k_2} \\
&+ \Bigl(\frac{e_T^2 F}{(k_{-1} + k_2)^2} + \frac{e_T^2 k_{-2}}{k_{-1} + k_2}\Bigr) t\Bigr).
\end{aligned}
$$
