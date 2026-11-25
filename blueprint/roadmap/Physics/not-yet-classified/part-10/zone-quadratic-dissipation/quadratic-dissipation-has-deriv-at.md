# Quadratic dissipation identity for thermal zones

Let $\iota$ be a finite set of zones with capacities $C_i$, symmetric conductances $G_{ij} = G_{ji}$, boundary conductances $g_i$, outdoor temperature $T_{\mathrm{out}}$ and heating powers $P_i$. Suppose each $T_i$ has derivative $\dot T_i$ at time $t$ and

$$C_i \dot T_i = \sum_j G_{ij}(T_j(t) - T_i(t)) + g_i (T_{\mathrm{out}} - T_i(t)) + P_i(t)$$

for every $i$. Then $s \mapsto \frac12 \sum_i C_i (T_i(s) - T_{\mathrm{out}})^2$ has derivative

$$-\Bigl(\frac12 \sum_{i,j} G_{ij} (T_j(t) - T_i(t))^2 + \sum_i g_i (T_i(t) - T_{\mathrm{out}})^2\Bigr) + \sum_i (T_i(t) - T_{\mathrm{out}})\,P_i(t)$$

at $t$.
