# Log-linear inactivation under time-varying temperature

Take the empirical inactivation rate $k(T) = \frac{\ln 10}{D_{\mathrm{ref}}}\,10^{(T - T_{\mathrm{ref}})/z}$ with $D_{\mathrm{ref}}, z > 0$,
temperature differences on the scale of $z$ and one time unit. For a continuous temperature history on a finite horizon and $N_0 > 0$,
the unique solution of $N' = -k(T(t))N$, $N(0) = N_0$, is $N(t) = N_0 \exp\bigl(-\int_0^t k(T(s))\,ds\bigr) > 0$, and the decimal
reduction is $\log_{10}(N_0/N(t)) = F(t)/D_{\mathrm{ref}}$ with $F(t) = \int_0^t 10^{(T(s) - T_{\mathrm{ref}})/z}\,ds$. Here $N$ is a
concentration or mean, not an integer count of survivors; product safety and count inference are outside this result.

## Depends on

## Proof depends on

## Sources

- *Principles of Food Processing and Preservation*, module "Thermal death time curves", sections 6.4–6.8: decimal reduction time, $z$-value and $F$-value, <https://ebooks.inflibnet.ac.in/ftp1/chapter/thermal-death-time-curves/>.
