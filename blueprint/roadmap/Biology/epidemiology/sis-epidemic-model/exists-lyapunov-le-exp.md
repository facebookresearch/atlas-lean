# For $R_0 > 1$, exponential decay of the Lyapunov function along solutions from the open segment

Let $0 < \gamma < \beta$ and $N > 0$, and let $(S, I)$ be a [solution of the SIS system](is-solution.md) with
$S(0) + I(0) = N$, $S(0) > 0$ and $I(0) > 0$. Then there is $c > 0$ such that the
[Goh–Volterra Lyapunov function](lyapunov.md) satisfies

$$V(S(t), I(t)) \le V(S(0), I(0))\, e^{-c t} \quad \text{for every } t \ge 0.$$

The rate depends on the solution; the proof takes $c = \beta m / N$, where
$m = I^* \exp(-(V(S(0), I(0)) + I^*)/I^*)$ with $I^* = N(1 - \gamma/\beta)$ is the lower bound on
$I$ from [persistence](persistence.md).
