# Nodal complex power

For a network with $n_N$ nodes and $n_E$ branches, a real incidence matrix $B \in \mathbb{R}^{n_N \times n_E}$, complex node voltages $V \in \mathbb{C}^{n_N}$, branch admittances $y \in \mathbb{C}^{n_E}$ and shunt admittances $y^s \in \mathbb{C}^{n_N}$, let $\Delta_e = \sum_u B_{ue} V_u$ be the branch drops and

$$I_v = \sum_{e=1}^{n_E} B_{ve}\, y_e\, \Delta_e + y^s_v V_v$$

the current injected at node $v$ into the branch and shunt network. The complex power supplied by node $v$ is

$$S_v = V_v\, \overline{I_v},$$

in the root-mean-square convention; it is a per-phase quantity.
