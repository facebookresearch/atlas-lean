# Log-linear inactivation under time-varying temperature

Let $D_{\mathrm{ref}}$, $T_{\mathrm{ref}}$ and $z$ be real numbers and take the [log-linear inactivation rate](rate.md)
$k(\theta) = \frac{\ln 10}{D_{\mathrm{ref}}}\,10^{(\theta - T_{\mathrm{ref}})/z}$. Let the temperature history $T$ be continuous
on $[0, t_f]$ and let $N_0 > 0$. Then $N(t) = N_0 \exp\bigl(-\int_0^t k(T(s))\,ds\bigr)$ satisfies $N(0) = N_0$ and
$N'(t) = -k(T(t))\,N(t)$ for $t \in [0, t_f]$, the derivative being taken within $[0, t_f]$. It is the only such function:
every $M$ with $M(0) = N_0$ and derivative $-k(T(t))\,M(t)$ within $[0, t_f]$ at each $t \in [0, t_f]$ equals $N$ on
$[0, t_f]$. For $t_f > 0$ these derivatives are one-sided at the endpoints. For $t_f = 0$ every number is a derivative within
$\{0\}$, so the equation imposes no condition and uniqueness rests on $M(0) = N_0$ alone; for $t_f < 0$ the interval is empty
and only $N(0) = N_0$ remains. Moreover, for $t \in [0, t_f]$, $N(t) > 0$ and the decimal reduction is

$$\log_{10}\frac{N_0}{N(t)} = \frac{F(t)}{D_{\mathrm{ref}}},$$

where $F(t) = \int_0^t 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$ is the [F-value](f-value.md) of the history. No sign condition on
$D_{\mathrm{ref}}$ or $z$ is needed, reading a division by zero as $0$.

In the model, $D_{\mathrm{ref}} > 0$ is the decimal reduction time at the reference temperature $T_{\mathrm{ref}}$, $z > 0$ is
the temperature rise that divides it by ten, and $F(t)$ is the time at $T_{\mathrm{ref}}$ with the same lethal effect.
Temperatures and $z$ share one unit, and times and $D_{\mathrm{ref}}$ share another. Here $N$ is a concentration or
mean, not an integer count of survivors; product safety and count inference are outside this result.

For every such $M$, the product $M(t)\exp\bigl(\int_0^t k(T(s))\,ds\bigr)$ has derivative zero within $[0, t_f]$, so it keeps
its value $N_0$ at $0$. The decimal reduction follows from $\int_0^t k(T(s))\,ds = \ln 10 \cdot F(t)/D_{\mathrm{ref}}$.

## Sources

- Aparna Kuna, *Principles of the Food Processing & Preservation*, module "Thermal death time curves", sections 6.4–6.8: decimal reduction time, $z$-value and $F$-value, each at a constant temperature, <https://ebooks.inflibnet.ac.in/ftp1/chapter/thermal-death-time-curves/>.
