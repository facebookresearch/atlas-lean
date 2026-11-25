# Scaled ideal-buck averaging bound

Let $L, C, R, I_{\mathrm{ref}}, V_{\mathrm{ref}} > 0$, $T \ge 0$, $\varepsilon > 0$, and let the duty $d$ take values in $[0,1]$ on $[0,T]$ and be $L_d$-Lipschitz there. Let $s$ be the PWM signal with cycle length $\varepsilon$: on cycle $k = \lfloor t/\varepsilon \rfloor$ it is $1$ while $t - k\varepsilon < d(k\varepsilon)\,\varepsilon$ and $0$ otherwise. Let $i, v$ (switched) and $\bar\imath, \bar v$ (averaged) be continuous on $[0,T]$ and satisfy, for $t \in [0,T]$,

$$i(t) = i_0 + \int_0^t \frac{s(u)V_{\mathrm{in}} - v(u)}{L}\,du, \qquad v(t) = v_0 + \int_0^t \frac{i(u) - v(u)/R}{C}\,du,$$

and the same equations for $\bar\imath, \bar v$ with initial values $\bar\imath_0, \bar v_0$ and $d$ in place of $s$. Then for every $t \in [0,T]$, $|i(t) - \bar\imath(t)| \le I_{\mathrm{ref}} B$ and $|v(t) - \bar v(t)| \le V_{\mathrm{ref}} B$, where

$$B = e^{\kappa T}\left(\max\left(\frac{|i_0 - \bar\imath_0|}{I_{\mathrm{ref}}}, \frac{|v_0 - \bar v_0|}{V_{\mathrm{ref}}}\right) + \frac{|V_{\mathrm{in}}|}{L I_{\mathrm{ref}}}\,\varepsilon\left(1 + \frac{L_d T}{2}\right)\right), \qquad \kappa = \max\left(\frac{V_{\mathrm{ref}}}{L I_{\mathrm{ref}}}, \frac{I_{\mathrm{ref}}}{C V_{\mathrm{ref}}} + \frac{1}{RC}\right).$$
