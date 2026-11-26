# Dissipation identity for the zone heat model

Let finitely many zones have capacities $C_i$, symmetric conductances $G_{ij} = G_{ji}$, outdoor conductances $g_i$, outdoor temperature $T_{out}$ and inputs $P_i(t)$, and let differentiable temperatures $T_i$ satisfy $C_i T_i' = \sum_j G_{ij}(T_j - T_i) + g_i(T_{out} - T_i) + P_i$. Then

$$\frac{d}{dt}\,\frac12\sum_i C_i (T_i - T_{out})^2 = -\Big(\frac12\sum_{i,j} G_{ij}(T_j - T_i)^2 + \sum_i g_i (T_i - T_{out})^2\Big) + \sum_i (T_i - T_{out}) P_i.$$
