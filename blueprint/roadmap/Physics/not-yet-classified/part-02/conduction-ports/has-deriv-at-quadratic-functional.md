# Quadratic Lyapunov identity for a conduction network

Let $\iota$ be a finite set of zones with capacities $C_i$ and symmetric conductances $G_{ij} = G_{ji}$. Suppose each temperature $T_i$ has derivative $\dot T_i$ at time $t$ and the balance $C_i \dot T_i = \sum_j G_{ij}(T_j(t) - T_i(t))$ holds for every $i$ (no boundary conductance or external heating). Then $\tau \mapsto \sum_i C_i T_i(\tau)^2/2$ has derivative

$$-\sum_i \sum_j \frac{G_{ij}\,(T_i(t) - T_j(t))^2}{2}$$

at $t$.
