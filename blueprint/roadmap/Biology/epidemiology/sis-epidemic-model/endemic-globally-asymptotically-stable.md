# For $R_0 > 1$, global asymptotic stability of the endemic equilibrium on the open segment

Let $\gamma > 0$, $R_0 = \beta/\gamma > 1$ and $N > 0$, and let
$(S^*, I^*) = (N\gamma/\beta,\ N(1 - \gamma/\beta))$. For solutions $(S, I)$ of the
[SIS system](is-solution.md) starting in the open segment $\{S + I = N,\ S > 0,\ I > 0\}$, that is,
with $S(0) + I(0) = N$, $S(0) > 0$ and $I(0) > 0$, both of the following hold.

- Stability: for every $\varepsilon > 0$ there is $\delta > 0$ such that every such solution with
  $d((S(0), I(0)), (S^*, I^*)) < \delta$ satisfies $d((S(t), I(t)), (S^*, I^*)) < \varepsilon$ for
  every $t \ge 0$, where $d((a, b), (a', b')) = \max(|a - a'|, |b - b'|)$ is the maximum distance.
- Attractivity: every such solution satisfies $(S(t), I(t)) \to (S^*, I^*)$ as $t \to \infty$.

Both facts are proved with the [Goh–Volterra Lyapunov function](lyapunov.md).
