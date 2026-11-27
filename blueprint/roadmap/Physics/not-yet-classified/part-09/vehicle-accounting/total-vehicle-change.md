# Total vehicle change

Consider cells $0, \dots, n-1$ with densities $k_i$ and face fluxes $F_i$ between cell $i - 1$ and cell $i$, where $F_0$ is the external inflow and $F_n$ the external outflow. For cell length $\Delta x > 0$ and any time step $\Delta t$, under the conservative update $k_i' = k_i + (\Delta t / \Delta x)(F_i - F_{i+1})$, the total vehicle count changes by exactly

$$\sum_{i=0}^{n-1} \Delta x\,(k_i' - k_i) = \Delta t\,(F_0 - F_n).$$
