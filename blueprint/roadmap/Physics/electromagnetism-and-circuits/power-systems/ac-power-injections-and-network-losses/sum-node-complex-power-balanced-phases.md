# A balanced drive makes each node supply three times its phase power

For natural numbers $n_N$ and $n_E$, a real $n_N \times n_E$ matrix $B$, node voltages
$V \in \mathbb{C}^{n_N}$, branch admittances $y$ and shunt admittances $y^s$, drive the network, for
each phase $p$, with the voltages $V^{(p)}_w$ of the
[balanced phase sets](../balanced-three-phase-power/balanced-phases.md)
$(V_w, \alpha^2 V_w, \alpha V_w)$, $\alpha = e^{2\pi i/3}$, of the node voltages. Then at every node
$v$ the three phases together supply three times the per-phase power:

$$\sum_{p} S_v\bigl(V^{(p)}\bigr) = 3\, S_v(V),$$

where $S_v(V)$ is the [complex power supplied by node](node-complex-power.md) $v$ at the voltages
$V$, with the same $B$, $y$ and $y^s$ in every phase. Each phase multiplies all voltages and
currents by the same unit phase factor, which leaves $V_v \overline{I_v}$ unchanged.
