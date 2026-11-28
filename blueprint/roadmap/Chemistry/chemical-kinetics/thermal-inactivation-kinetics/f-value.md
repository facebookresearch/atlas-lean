# F-value of a temperature history

For a temperature history $T$, the F-value up to time
$t$ is $F(t) = \int_0^t 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$: the time at the reference
temperature $T_{\mathrm{ref}}$ with the same lethal effect in the log-linear model with $z$-value
$z$. The integral is oriented, $F(t) = -\int_t^0 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$ for $t < 0$,
and it is $0$ when the integrand is not integrable between $0$ and $t$; a division by zero is read
as $0$.
