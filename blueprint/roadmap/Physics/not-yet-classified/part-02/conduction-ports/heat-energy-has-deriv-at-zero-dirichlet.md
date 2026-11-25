# Energy derivative of the heat equation with zero Dirichlet data

Let $L \ge 0$ and fix a time $t$. Suppose that for every $x \in [0, L]$ the function $u$ has time derivative $u_t(t,x)$, space derivative $u_x(t,x)$ and second space derivative $u_{xx}(t,x)$, with $u_t = D u_{xx} + f$ there; that $u(t,\cdot)$, $u_x(t,\cdot)$, $u_{xx}(t,\cdot)$ are continuous on $[0, L]$; that $E(\tau) = \int_0^L u(\tau,x)^2/2\,dx$ has derivative $\int_0^L u\,u_t\,dx$ at $t$ with $u(t,\cdot)u_t(t,\cdot)$ integrable on $[0, L]$; and that $u(t,0) = u(t,L) = 0$. Then

$$E'(t) = -D\int_0^L u_x(t,x)^2\,dx + \int_0^L u(t,x) f(t,x)\,dx.$$
