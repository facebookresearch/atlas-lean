# Total supplied reactive power is minus the susceptive terms

Let $n_N$ and $n_E$ be natural numbers, the numbers of nodes and branches, let $B$ be a real
$n_N \times n_E$ matrix, in the model the signed node–branch incidence matrix, and let
$V \in \mathbb{C}^{n_N}$ be the root-mean-square node-voltage phasors, $y \in \mathbb{C}^{n_E}$ the
branch admittances and $y^s \in \mathbb{C}^{n_N}$ the shunt admittances. Write
$d_e = \sum_v B_{ve} V_v$ for the [branch drops](branch-drop.md) and $S_v = V_v \overline{I_v}$ for
the [complex power supplied by node](node-complex-power.md) $v$, with $I_v$ the
[injected current](node-injection.md). Then the total supplied reactive power is

$$
\sum_v \operatorname{Im} S_v = -\sum_e \operatorname{Im}(y_e)\, |d_e|^2 -
\sum_v \operatorname{Im}(y^s_v)\, |V_v|^2,
$$

the imaginary part of the [complex balance](total-complex-power-eq-branch-add-shunt.md), in which
conjugation reverses the sign of each imaginary part (susceptance). No condition on the data is
needed.
