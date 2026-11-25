# Sharp switched-to-averaged error bound at constant duty

Let $E$ be a finite-dimensional real normed space, $A : E \to E$ a continuous linear operator with operator norm $\|A\|$, $b \in E$ a fixed input direction and $c : \mathbb{R} \to E$ a forcing term. Assume $c$ is continuous. Let $T \ge 0$, $\varepsilon > 0$ and $c_0 \in [0, 1]$, and let $s_\varepsilon$ be the pulse-width signal with switching-cycle length $\varepsilon$ and constant duty $c_0$: on the cycle $k = \lfloor t/\varepsilon \rfloor$, $s_\varepsilon(t) = 1$ if $t - k\varepsilon < c_0\,\varepsilon$ and $s_\varepsilon(t) = 0$ otherwise. Let $x_0, y_0 \in E$ and let $x, y : \mathbb{R} \to E$ satisfy, for all $t \in [0, T]$,

$$x(t) = x_0 + \int_0^t \big(A x(u) + s_\varepsilon(u)\, b + c(u)\big)\, du, \qquad y(t) = y_0 + \int_0^t \big(A y(u) + c_0\, b + c(u)\big)\, du.$$

Then for every $t \in [0, T]$

$$\|x(t) - y(t)\| \le e^{\|A\| T} \big(\|x_0 - y_0\| + \|b\|\, c_0 (1 - c_0)\, \varepsilon\big).$$
