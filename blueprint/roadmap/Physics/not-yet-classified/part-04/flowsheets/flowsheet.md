# Process flowsheet

A process flowsheet over a finite set of process units and a set of species consists of, for each species $s$, unit $u$ and time $t$: a holdup $H_{s,u}(t)$, internal transfer rates $T_{s,i\to j}(t)$ between units, an external inflow rate $I_{s,u}(t)$, an external outflow rate $O_{s,u}(t)$ and a generation rate $G_{s,u}(t)$, subject to the unit balance

$$H_{s,u}'(t) = \sum_j \bigl(T_{s,j\to u}(t) - T_{s,u\to j}(t)\bigr) + I_{s,u}(t) - O_{s,u}(t) + G_{s,u}(t)$$

for every $s$, $u$ and $t$. Each internal transfer thus appears once as an outflow and once as an inflow.
