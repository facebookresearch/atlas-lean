# Switched-to-averaged error bound for affine PWM systems

Let $E$ be a finite-dimensional real normed space, $A : E \to E$ a continuous linear operator with operator norm $\|A\|$, $b \in E$ a fixed input direction and $c : \mathbb{R} \to E$ a forcing term. Assume $c$ is continuous. Let $T \ge 0$, $\varepsilon > 0$, $L_d \ge 0$, and let $d : \mathbb{R} \to \mathbb{R}$ take values in $[0, 1]$ on $[0, T]$ and be $L_d$-Lipschitz on $[0, T]$. For $\varepsilon > 0$ and a duty function $d : \mathbb{R} \to \mathbb{R}$, the pulse-width signal $s_\varepsilon$ is defined on the switching cycle $k = \lfloor t/\varepsilon \rfloor$ by $s_\varepsilon(t) = 1$ if $t - k\varepsilon < d(k\varepsilon)\,\varepsilon$ and $s_\varepsilon(t) = 0$ otherwise. Let $x_0, y_0 \in E$ and let $x, y : \mathbb{R} \to E$ satisfy, for all $t \in [0, T]$,

$$x(t) = x_0 + \int_0^t \big(A x(u) + s_\varepsilon(u)\, b + c(u)\big)\, du, \qquad y(t) = y_0 + \int_0^t \big(A y(u) + d(u)\, b + c(u)\big)\, du.$$

Then for every $t \in [0, T]$

$$\|x(t) - y(t)\| \le e^{\|A\| T} \Big(\|x_0 - y_0\| + \|b\|\, \varepsilon \big(1 + \tfrac{L_d T}{2}\big)\Big).$$
