# Nodal reactive power injection equation

Consider a network with $n_N$ nodes and $n_E$ branches, a real incidence matrix $B \in \mathbb{R}^{n_N \times n_E}$, complex node voltages $V \in \mathbb{C}^{n_N}$, branch admittances $y \in \mathbb{C}^{n_E}$ and shunt admittances $y^s \in \mathbb{C}^{n_N}$. The branch voltage drop is $\Delta_e = \sum_{u} B_{ue} V_u$, the branch part of the injection at node $v$ is $I^{br}_v = \sum_{e} B_{ve}\, y_e\, \Delta_e$, the node injection is $I_v = I^{br}_v + y^s_v V_v$, and the complex power supplied at node $v$ is $S_v = V_v\,\overline{I_v}$. Then for every node $v$,

$$\operatorname{Im} S_v = \operatorname{Im}\!\big(V_v\,\overline{I^{br}_v}\big) - \operatorname{Im}(y^s_v)\,|V_v|^2.$$
