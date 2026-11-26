# RK4 step on the bath field via the stability polynomial

For $C, G, T_{\mathrm{amb}} \in \mathbb{R}$ let $f(t, T) = -G\,(T - T_{\mathrm{amb}})/C$, let $\tau = C/G$, and let

$$R(z) = 1 + z + \frac{z^2}{2} + \frac{z^3}{6} + \frac{z^4}{24}.$$

For all real $t$, $T$ and $dt$, one step of size $dt$ from $(t, T)$ of the classical fourth-order Runge–Kutta method applied to $f$ equals

$$T_{\mathrm{amb}} + (T - T_{\mathrm{amb}})\, R(z), \qquad z = -\frac{1}{\tau}\, dt.$$

No sign assumption is made: if $C = 0$ or $G = 0$ then $\tau = 0$ and $z = 0$ under the convention $x/0 = 0$, and both sides equal $T$.
