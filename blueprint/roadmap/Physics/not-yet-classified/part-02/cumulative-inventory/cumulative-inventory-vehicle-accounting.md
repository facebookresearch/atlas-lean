# Cumulative vehicle inventory of a cell chain

Let $\Delta t \ge 0$, $\Delta x > 0$, and let densities $k_j(i)$ and face fluxes $F_j(i)$ satisfy $k_{j+1}(i) = k_j(i) + \frac{\Delta t}{\Delta x}(F_j(i) - F_j(i+1))$ for all $j, i$. Then for $N$ cells and $n$ steps, $\sum_{i<N} \Delta x\,k_n(i) = \sum_{i<N} \Delta x\,k_0(i) + \sum_{j<n} \Delta t\,F_j(0) - \sum_{j<n} \Delta t\,F_j(N)$.
