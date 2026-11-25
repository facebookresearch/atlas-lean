# PWM discrepancy at half duty after half a cycle

For a cycle length $\varepsilon > 0$ and a duty function $d$, the PWM signal $s_\varepsilon$ equals $1$ at time $u$ if $u - k\varepsilon < d(k\varepsilon)\,\varepsilon$ with $k = \lfloor u/\varepsilon \rfloor$, and $0$ otherwise; the discrepancy primitive is $q(t) = \int_0^t \bigl(s_\varepsilon(u) - d(u)\bigr)\,du$. With cycle length $\varepsilon = 1$ and constant duty $d \equiv 1/2$,
$$q(1/2) = \tfrac14.$$
