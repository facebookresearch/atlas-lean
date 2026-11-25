# PWM averaging bound

For a cycle length $\varepsilon > 0$ and a duty function $d$, the PWM signal $s_\varepsilon$ equals $1$ at time $u$ if $u - k\varepsilon < d(k\varepsilon)\,\varepsilon$ with $k = \lfloor u/\varepsilon \rfloor$, and $0$ otherwise; the discrepancy primitive is $q(t) = \int_0^t \bigl(s_\varepsilon(u) - d(u)\bigr)\,du$. Let $T \ge 0$, $\varepsilon > 0$, $L_d \ge 0$, and let $d$ take values in $[0, 1]$ on $[0, T]$ and be $L_d$-Lipschitz on $[0, T]$. Then for every $t \in [0, T]$,
$$|q(t)| \le \varepsilon \Bigl(1 + \frac{L_d T}{2}\Bigr).$$
