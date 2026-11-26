# One-stage Runge–Kutta step on the bath field is the Euler step

For $C, G, T_{\mathrm{amb}} \in \mathbb{R}$ let $f(t, T) = Q(T)/C$ with $Q(T) = -G\,(T - T_{\mathrm{amb}})$. For all real $t$, $T$ and $dt$, one step of size $dt$ from $(t, T)$ of the one-stage explicit Runge–Kutta method (explicit Euler) applied to $f$ equals

$$T + dt\,\frac{Q(T)}{C}.$$

No sign or nonvanishing assumption is made; for $C = 0$ both sides equal $T$ under the convention $x/0 = 0$.
