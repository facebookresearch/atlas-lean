# Cell-transmission update preserves admissible densities

For speeds $v, w > 0$, jam density $k_j > 0$, densities $k, k_{in}, k_{out} \in [0, k_j]$, time step $\Delta t \ge 0$, cell length $\Delta x > 0$ and the CFL condition $\frac{\Delta t}{\Delta x} \max(v, w) \le 1$, the updated density $k + \frac{\Delta t}{\Delta x}\big(F(k_{in}, k) - F(k, k_{out})\big)$ lies in $[0, k_j]$, where $F$ is the face flux (minimum of upstream demand and downstream supply) of the triangular fundamental diagram.
