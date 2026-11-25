# Temperature drop across one layer

For a layered wall of area $A$ carrying heat rate $Q$, with inner fluid temperature $T_{\mathrm{in}}$, inner film coefficient $h_{\mathrm{in}}$, and layers of thickness $L_i$ and conductivity $k_i$, let the temperature at interface $m$ be $T_m = T_{\mathrm{in}} - Q\big(1/(h_{\mathrm{in}} A) + \sum_{i < m} L_i/(k_i A)\big)$. Then for every $m$, adjacent interface temperatures differ by the drop across layer $m$: $T_m - T_{m+1} = Q\, L_m / (k_m A)$, where every quotient with zero denominator (such as $L_m/(k_m A)$ when $k_m A = 0$) is $0$.
