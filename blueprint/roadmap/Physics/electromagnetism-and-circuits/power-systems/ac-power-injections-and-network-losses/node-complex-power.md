# Complex power supplied by a node

For natural numbers $n_N$ and $n_E$, a real $n_N \times n_E$ matrix $B$, node voltages
$V \in \mathbb{C}^{n_N}$, branch admittances $y \in \mathbb{C}^{n_E}$, shunt admittances
$y^s \in \mathbb{C}^{n_N}$ and a node $v$, the complex power supplied by $v$ is
$S_v = V_v \overline{I_v}$, the [complex power](../balanced-three-phase-power/complex-power.md) of
the voltage $V_v$ and the [injected current](node-injection.md) $I_v$, for root-mean-square phasors
and with no factor $1/2$.

Since $I_v$ is the current leaving the node into the branches and the shunt, $S_v$ is the power that
the network absorbs through node $v$. For example, one branch of admittance $1$ from node $0$ to
node $1$ ($B_{00} = 1$, $B_{10} = -1$) with $V = (1, 0)$ and no shunts gives $S_0 = 1$: node $0$
supplies the power the branch dissipates. Every node carries one phasor, so $S_v$ is a per-phase
quantity; in [balanced three-phase operation](sum-node-complex-power-balanced-phases.md) the three
phases supply $3 S_v$.
