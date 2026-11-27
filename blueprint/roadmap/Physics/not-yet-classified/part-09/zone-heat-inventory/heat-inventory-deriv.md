# Zone heat inventory balance

Let the zones form a finite set, with capacities $C_i$, symmetric conductances $G_{ij} = G_{ji}$, and zone temperatures $T_i$ differentiable with derivative $\dot T_i(t)$ at every $t$. If every zone satisfies $C_i \dot T_i(t) = \sum_j G_{ij}\big(T_j(t) - T_i(t)\big) + b_i(t) + P_i(t)$, then the total heat inventory $\sum_i C_i T_i$ has derivative $\sum_i \big(b_i(t) + P_i(t)\big)$ at every $t$.
