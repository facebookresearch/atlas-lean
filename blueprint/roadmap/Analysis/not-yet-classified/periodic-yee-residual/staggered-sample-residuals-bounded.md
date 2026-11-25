# Staggered-sample consistency of the periodic Yee scheme

Let $N > 0$, $h > 0$, $\Delta t > 0$, $c > 0$, $L = Nh$, $M_t \ge 0$, $M_x \ge 0$. Let $(u, v)$ solve $u_t = c\,v_x$, $v_t = c\,u_x$, be $L$-periodic in $x$, be three times continuously differentiable in each variable separately, and have all third time derivatives bounded by $M_t$ and all third space derivatives bounded by $M_x$ in absolute value. With staggered samples $U^n_j = u(n\Delta t, jh)$, $V^n_j = v(n\Delta t - \Delta t/2, jh - h/2)$, periodic forward and backward differences $D_+$, $D_-$, and residuals

$$r_u^n = U^{n+1} - U^n - c\,\Delta t\,D_+ V^{n+1}, \qquad r_v^n = V^{n+1} - V^n - c\,\Delta t\,D_- U^n,$$

for every $n$ both $\lVert r_u^n \rVert_h$ and $\lVert r_v^n \rVert_h$ are at most

$$\frac{\sqrt{L}\,\Delta t\,(M_t\,\Delta t^2 + c\,M_x\,h^2)}{24},$$

where $\lVert w \rVert_h = \sqrt{h\sum_j w_j^2}$.
