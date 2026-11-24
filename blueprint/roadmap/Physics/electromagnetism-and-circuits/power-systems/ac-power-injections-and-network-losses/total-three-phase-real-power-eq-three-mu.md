# Balanced three-phase real power is three times the per-phase losses

Let $n_N$ and $n_E$ be natural numbers, the numbers of nodes and branches, let $B$ be a real
$n_N \times n_E$ matrix, in the model the signed node–branch incidence matrix, and let
$V \in \mathbb{C}^{n_N}$ be the root-mean-square node-voltage phasors, $y \in \mathbb{C}^{n_E}$ the
branch admittances and $y^s \in \mathbb{C}^{n_N}$ the shunt admittances. Write
$d_e = \sum_v B_{ve} V_v$ for the [branch drops](branch-drop.md) and $S_v = V_v \overline{I_v}$ for
the [complex power supplied by node](node-complex-power.md) $v$, with $I_v$ the
[injected current](node-injection.md). Driving the network in each phase $p$ with the
[balanced phase sets](../balanced-three-phase-power/balanced-phases.md) $V^{(p)}_w$ of the node
voltages, as in [balanced operation at a node](sum-node-complex-power-balanced-phases.md), the real
power the three phases supply over all nodes is

$$
\sum_v \operatorname{Re} \sum_p S_v\bigl(V^{(p)}\bigr) =
3 \Bigl(\sum_e \operatorname{Re}(y_e)\, |d_e|^2 + \sum_v \operatorname{Re}(y^s_v)\, |V_v|^2\Bigr),
$$

three times the per-phase [real power balance](total-real-power-eq-branch-add-shunt-los.md), with
$d_e$ the drops at the voltages $V$. No condition on the data is needed.
