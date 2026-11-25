# Thermal storage balance

Let a finite set of nodes have capacities $C_i$, symmetric conductances $G_{ij} = G_{ji}$, sources $Q_i$ and temperatures $T_i(\tau)$ with $T_i'(t) = \dot T_i$. If every node obeys $C_i \dot T_i = \sum_j G_{ij}(T_j(t) - T_i(t)) + Q_i$, then the stored heat $\sum_i C_i T_i(\tau)$ has derivative $\sum_i Q_i$ at $t$: conduction between nodes cancels.
