# Real power at a node: branch injection plus shunt conductance term

Let $n_N$ and $n_E$ be natural numbers, the numbers of nodes and branches, let $B$ be a real
$n_N \times n_E$ matrix, in the model the signed node–branch incidence matrix, and let
$V \in \mathbb{C}^{n_N}$ be the root-mean-square node-voltage phasors, $y \in \mathbb{C}^{n_E}$ the
branch admittances and $y^s \in \mathbb{C}^{n_N}$ the shunt admittances. Write
$d_e = \sum_v B_{ve} V_v$ for the [branch drops](branch-drop.md) and $S_v = V_v \overline{I_v}$ for
the [complex power supplied by node](node-complex-power.md) $v$, with $I_v$ the
[injected current](node-injection.md). Then at every node $v$,

$$
\operatorname{Re} S_v =
\operatorname{Re}\Bigl(V_v\, \overline{\textstyle\sum_e B_{ve}\, y_e d_e}\Bigr) +
\operatorname{Re}(y^s_v)\, |V_v|^2,
$$

the real power carried by the branch currents plus the shunt conductance times the squared voltage
magnitude. No condition on the data is needed.
