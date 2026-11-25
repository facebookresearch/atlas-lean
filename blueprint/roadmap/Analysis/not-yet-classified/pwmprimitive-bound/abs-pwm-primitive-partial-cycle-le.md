# PWM discrepancy over a partial cycle

For a cycle length $\varepsilon > 0$ and a duty function $d$, the PWM signal $s_\varepsilon$ equals $1$ at time $u$ if $u - k\varepsilon < d(k\varepsilon)\,\varepsilon$ with $k = \lfloor u/\varepsilon \rfloor$, and $0$ otherwise; the discrepancy primitive is $q(t) = \int_0^t \bigl(s_\varepsilon(u) - d(u)\bigr)\,du$. Let $\varepsilon > 0$ and let $d$ take values in $[0, 1]$ on $[0, T]$. Then for every $t \in [0, T]$,
$$\Bigl| \int_{\lfloor t/\varepsilon \rfloor \varepsilon}^{t} \bigl(s_\varepsilon(u) - d(u)\bigr)\, du \Bigr| \le \varepsilon.$$
