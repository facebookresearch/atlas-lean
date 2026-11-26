# PWM primitive for the indicator of the rationals

Let $\varepsilon > 0$ be rational and let the duty $d : \mathbb{R} \to \mathbb{R}$ be the indicator of the rationals: $d(u) = 1$ for rational $u$ and $0$ otherwise, so $d$ takes values in $[0, 1]$ and is Lipschitz on no nontrivial interval. The switching signal $s_\varepsilon(t) = 1$ if $t - k\varepsilon < d(k\varepsilon)\,\varepsilon$ with $k = \lfloor t/\varepsilon \rfloor$, and $0$ otherwise, is then $1$ at every real $t$: every sample point $k\varepsilon$ is rational, so $d(k\varepsilon) = 1$. For every $t \ge 0$ the primitive of the discrepancy is

$$q(t) = \int_0^t \bigl(s_\varepsilon(u) - d(u)\bigr)\,du = t,$$

because $d = 0$ almost everywhere.
