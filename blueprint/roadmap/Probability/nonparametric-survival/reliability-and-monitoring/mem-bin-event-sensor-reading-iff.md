# Bin membership of the sensor reading of a linear damage path

Let $\Omega$ be a finite scenario type, $g \ne 0$ a gain, $b$ an offset, $i_0$ a monitored
component, $d_0(i, \omega)$ and $r(i, \omega)$ initial damages and rates of any sign,
$\varepsilon(\omega)$ the sensor errors, $t \ge 0$ a time and $z_{\mathrm{lo}}$, $z_{\mathrm{hi}}$
real bounds. A scenario $\omega$ lies in the [bin event](bin-event.md) of the
[sensor reading](sensor-reading.md) of the linear damage of component $i_0$ at time $t$ if and only
if

$$
z_{\mathrm{lo}} \le g\, \bigl(d_0(i_0, \omega) + r(i_0, \omega)\, t\bigr) + b +
\varepsilon(\omega) \le z_{\mathrm{hi}}.
$$

In the physical reading the rates are nonnegative; the equivalence holds for rates of any sign.
