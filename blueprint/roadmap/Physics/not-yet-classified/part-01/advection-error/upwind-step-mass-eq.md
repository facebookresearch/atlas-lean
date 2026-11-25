# Upwind step conserves mass

Consider $n \ge 1$ periodic cells of length $dx > 0$ and cross-section $A > 0$, a speed $v \ge 0$ and any time step $dt$ (any Courant number). If $c'$ is obtained from $c$ by the conservative step $A\,dx\,c'_i = A\,dx\,c_i + dt\,(F_i - F_{i+1})$ with the upwind face flux $F_i = A\,(\max(v,0)\,c_{i-1} + \min(v,0)\,c_i)$, then the total mass is preserved:

$$\sum_i A\,dx\,c'_i = \sum_i A\,dx\,c_i.$$
