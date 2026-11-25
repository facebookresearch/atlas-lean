# Switched-to-averaged error bound from a bounded discrepancy primitive

Let $E$ be a finite-dimensional real normed space, $A : E \to E$ a continuous linear operator with operator norm $\|A\|$, $b \in E$ a fixed input direction and $c : \mathbb{R} \to E$ a forcing term. Let $T \ge 0$, $Q \ge 0$, $s, d : \mathbb{R} \to \mathbb{R}$, $x_0, y_0 \in E$, and let $x, y : \mathbb{R} \to E$ satisfy, for all $t \in [0, T]$,

$$x(t) = x_0 + \int_0^t \big(A x(u) + s(u)\, b + c(u)\big)\, du, \qquad y(t) = y_0 + \int_0^t \big(A y(u) + d(u)\, b + c(u)\big)\, du,$$

where both integrands are interval integrable on $[0, T]$. If $\left|\int_0^t (s(u) - d(u))\, du\right| \le Q$ for all $t \in [0, T]$, then for every $t \in [0, T]$

$$\|x(t) - y(t)\| \le e^{\|A\| T} \big(\|x_0 - y_0\| + \|b\|\, Q\big).$$
