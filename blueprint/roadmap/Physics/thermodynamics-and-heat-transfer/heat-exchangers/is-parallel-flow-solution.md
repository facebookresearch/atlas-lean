# Parallel-flow exchanger solution

For real $C_h, C_c, K, L, T_{h,i}, T_{c,i}$ and functions $T_h, T_c : \mathbb{R} \to \mathbb{R}$, the pair $(T_h, T_c)$ is a parallel-flow solution on $[0, L]$ with both inlets at $x = 0$ when $T_h(0) = T_{h,i}$, $T_c(0) = T_{c,i}$, and at every $x \in [0, L]$ the functions $y \mapsto C_h T_h(y)$ and $y \mapsto C_c T_c(y)$ have derivatives within $[0, L]$ (one-sided at the ends)

$$\big(C_h T_h\big)'(x) = -K\,\big(T_h(x) - T_c(x)\big), \qquad \big(C_c T_c\big)'(x) = K\,\big(T_h(x) - T_c(x)\big).$$
