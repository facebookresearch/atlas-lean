# A solution equal to the explicit one at $a$ stays equal through $b$

Let $V > 0$, $Q > 0$ and $k \ge 0$, let $c_{\mathrm{in}}$, $c_0$, $a$ and $b$ be real, and let
$c(t) = c_{\mathrm{ss}} + (c_0 - c_{\mathrm{ss}})\, e^{-(Q / V + k) t}$ be the explicit
[reactor concentration](solution.md), with $c_{\mathrm{ss}} = Q c_{\mathrm{in}} / (Q + kV)$. Let
$f$ be continuous on $[a, b]$ and have, at every $t \in [a, b)$, the derivative from the right

$$f'(t) = \frac{Q}{V} \bigl(c_{\mathrm{in}} - f(t)\bigr) - k\, f(t) ,$$

the reactor equation $V f' = Q (c_{\mathrm{in}} - f) - k V f$ divided by $V$. If $f(a) = c(a)$,
then $f(t) = c(t)$ for every $t \in [a, b]$. The initial condition is the value of the explicit
concentration at $a$; at $a = 0$ it reads $f(0) = c_0$. For $b < a$ the interval is empty.
