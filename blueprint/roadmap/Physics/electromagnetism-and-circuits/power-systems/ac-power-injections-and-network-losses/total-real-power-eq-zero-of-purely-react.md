# With purely reactive admittances the total real power is zero

Let $n_N$ and $n_E$ be natural numbers, the numbers of nodes and branches, let $B$ be a real
$n_N \times n_E$ matrix, in the model the signed node–branch incidence matrix, and let
$V \in \mathbb{C}^{n_N}$ be the root-mean-square node-voltage phasors, $y \in \mathbb{C}^{n_E}$ the
branch admittances and $y^s \in \mathbb{C}^{n_N}$ the shunt admittances. Write
$d_e = \sum_v B_{ve} V_v$ for the [branch drops](branch-drop.md) and $S_v = V_v \overline{I_v}$ for
the [complex power supplied by node](node-complex-power.md) $v$, with $I_v$ the
[injected current](node-injection.md). If $\operatorname{Re}(y_e) = 0$ for every branch $e$ and
$\operatorname{Re}(y^s_v) = 0$ for every node $v$, then the total supplied real power is zero:
$\sum_v \operatorname{Re} S_v = 0$, since every loss term of the
[real power balance](total-real-power-eq-branch-add-shunt-los.md) vanishes.
