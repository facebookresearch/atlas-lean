# For $R_0 > 1$, the infectives stay bounded away from zero

Let $0 < \gamma < \beta$ (so $R_0 = \beta/\gamma > 1$) and $N > 0$, and let $(S, I)$ be a
[solution of the SIS system](is-solution.md) with $S(0) + I(0) = N$, $S(0) > 0$ and $I(0) > 0$. Let
$I^* = N(1 - \gamma/\beta)$ and $V_0 = V(S(0), I(0))$, with $V$ the [Goh–Volterra Lyapunov function](lyapunov.md). Then
for every $t \ge 0$

$$I(t) \ge m = I^* \exp\left(-\frac{V_0 + I^*}{I^*}\right),$$

and $m > 0$ since $I^* > 0$. The bound depends on the solution through $V_0$.
