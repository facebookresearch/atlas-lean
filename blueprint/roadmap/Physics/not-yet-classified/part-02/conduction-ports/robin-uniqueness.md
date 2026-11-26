# Uniqueness for the source-free Robin heat problem

Let $D \ge 0$, $L > 0$, $k > 0$, $h_0 \ge 0$, $h_L \ge 0$ and $T_a$ be given, and let $u_1$, $u_2$ be fields with spatial-derivative fields $u_{1,x}$, $u_{2,x}$. Write $w = u_1 - u_2$ and $w_x = u_{1,x} - u_{2,x}$. Assume:

- for every $t \in (0, T)$ and $i = 1, 2$: $k u_{i,x}(t, 0) = h_0 (u_i(t, 0) - T_a)$ and $-k u_{i,x}(t, L) = h_L (u_i(t, L) - T_a)$;
- for every $t \in (0, T)$ the energy $E(t) = \int_0^L w(t, x)^2/2\,dx$ has derivative $-D \int_0^L w_x(t, x)^2\,dx + D\,\big(w(t, L) w_x(t, L) - w(t, 0) w_x(t, 0)\big)$;
- $E$ is continuous on $[0, T]$, and $w(t, \cdot)$ is continuous on $[0, L]$ for every $t \in [0, T]$;
- $u_1(0, x) = u_2(0, x)$ for every $x \in [0, L]$.

Then $u_1(t, x) = u_2(t, x)$ for all $t \in [0, T]$ and $x \in [0, L]$.
