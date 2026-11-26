# Heat energy derivative with boundary work

Let $L \ge 0$, $D$ real, and fix a time $t$. Suppose that for every $x \in [0, L]$: $\tau \mapsto u(\tau, x)$ has derivative $u_t(t, x)$ at $t$; $y \mapsto u(t, y)$ has derivative $u_x(t, x)$ at $x$; $y \mapsto u_x(t, y)$ has derivative $u_{xx}(t, x)$ at $x$; and $u_t(t, x) = D u_{xx}(t, x) + s(t, x)$. Suppose also that $u(t, \cdot)$, $u_x(t, \cdot)$ and $u_{xx}(t, \cdot)$ are continuous on $[0, L]$, that $x \mapsto u(t, x) u_t(t, x)$ is integrable on $[0, L]$, and that the energy $E(\tau) = \int_0^L u(\tau, x)^2/2 \, dx$ has derivative $\int_0^L u(t, x) u_t(t, x) \, dx$ at $t$. Then $E$ has derivative at $t$

$$-D \int_0^L u_x(t, x)^2 \, dx + D\big(u(t, L) u_x(t, L) - u(t, 0) u_x(t, 0)\big) + \int_0^L u(t, x) s(t, x) \, dx.$$
