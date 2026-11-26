# Discrepancy-primitive error bound with zero operator

Let $E$ be a finite-dimensional real normed space, $b, x_0, y_0 \in E$, $c : \mathbb{R} \to E$, $s, d : \mathbb{R} \to \mathbb{R}$ and $T, Q \ge 0$. Suppose that for every $t \in [0, T]$

$$x(t) = x_0 + \int_0^t \big(s(u)\,b + c(u)\big)\,du, \qquad y(t) = y_0 + \int_0^t \big(d(u)\,b + c(u)\big)\,du,$$

with both integrands interval integrable on $[0, T]$, and $\big|\int_0^t (s(u) - d(u))\,du\big| \le Q$. Then for every $t \in [0, T]$,

$$\|x(t) - y(t)\| \le \|x_0 - y_0\| + \|b\|\,Q.$$

This is the bounded-primitive estimate for the linear part $A = 0$, where the exponential factor is $1$; the initial mismatch is kept.
