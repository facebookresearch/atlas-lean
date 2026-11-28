# Constant duty keeps the PWM discrepancy below the carrier length

Let the pulse-width-modulated signal with carrier length $\varepsilon$ and duty $d$ be $s(t) = 1$ when $t - k\varepsilon < d(k\varepsilon)\, \varepsilon$ for $k = \lfloor t/\varepsilon \rfloor$, and $s(t) = 0$ otherwise, and let $q(t) = \int_0^t (s(u) - d(u))\, du$. Let $T \ge 0$, $\varepsilon > 0$ and a constant duty $d \equiv c$ with $c \in [0, 1]$. Then $|q(t)| \le \varepsilon$ for every $t \in [0, T]$.
