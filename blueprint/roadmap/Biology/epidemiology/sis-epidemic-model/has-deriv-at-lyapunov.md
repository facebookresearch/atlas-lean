# Derivative of the Lyapunov function along solutions

Let $0 < \gamma < \beta$ and $N > 0$, and let $(S, I)$ be a [solution of the SIS system](is-solution.md) with
$S(0) + I(0) = N$. At every time $t \ge 0$ with $S(t) > 0$ and $I(t) > 0$, the function
$s \mapsto V(S(s), I(s))$, with $V$ the [Goh–Volterra Lyapunov function](lyapunov.md), is differentiable at $t$ with

$$\frac{d}{dt} V(S(t), I(t)) = -\frac{\beta\, (S(t) - S^*)^2}{S(t)},$$

where $S^* = N\gamma/\beta$.
