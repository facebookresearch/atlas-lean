# For $R_0 > 1$, interior solutions converge to the endemic equilibrium

Let $\gamma > 0$ and $R_0 = \beta/\gamma > 1$, and let $(S, I)$ be a [solution of the SIS system](is-solution.md) starting
in the open segment $\{S + I = N,\ S > 0,\ I > 0\}$: $S(0) + I(0) = N$, $S(0) > 0$ and $I(0) > 0$
(so $N > 0$). Then, with $S^* = N\gamma/\beta$ and $I^* = N(1 - \gamma/\beta)$,

$$(S(t), I(t)) \to (S^*, I^*) \quad \text{as } t \to \infty.$$

The proof uses the [Goh–Volterra Lyapunov function](lyapunov.md).
