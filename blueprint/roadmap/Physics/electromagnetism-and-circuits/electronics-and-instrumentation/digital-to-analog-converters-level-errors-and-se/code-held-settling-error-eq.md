# Settling error against the actual level of a held code

Let $\tau > 0$ and $\Delta$ be real numbers, $e \colon \mathbb{Z} \to \mathbb{R}$, $k$ an integer
and $L = \Delta k + e(k)$ the [actual DAC level](dac-level.md) of code $k$. Let $t_0 < t_1$ and let
$y \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[t_0, t_1]$ and differentiable at every
$s \in (t_0, t_1)$ with $\tau\, y'(s) = L - y(s)$. Then for every $t \in [t_0, t_1]$

$$|y(t) - L| = |y(t_0) - L| \exp\left(-\frac{t - t_0}{\tau}\right).$$

This is the [settling-error law](settling-error-eq.md) with held level $u = L$: the error is
measured against the actual level of the code, not its ideal level $\Delta k$.
