# Total vehicle change equals the discrete flux balance

For $n \in \mathbb N$, cell densities $k_i$, face fluxes $F_i$, a time step $dt$ and a cell width $dx > 0$, after one conservative update $k_i' = k_i + (dt/dx)(F_i - F_{i+1})$,

$$\sum_{i<n} dx\,(k_i' - k_i) = dx\,dt \sum_{i<n} \left(-\frac{F_{i+1} - F_i}{dx}\right).$$
