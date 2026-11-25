# The bus admittance matrix maps voltages to nodal current injections

For natural numbers $n$ and $m$, every real matrix $B \in \mathbb{R}^{n \times m}$, every
$V \in \mathbb{C}^n$, $y \in \mathbb{C}^m$ and $y^{\mathrm{sh}} \in \mathbb{C}^n$, and every bus
$k$, the [bus admittance matrix](bus-admittance.md)
$Y = B\, \mathrm{diag}(y)\, B^{\mathsf T} + \mathrm{diag}(y^{\mathrm{sh}})$ satisfies

$$(Y V)_k = \sum_{e} B_{ke}\, y_e\, (B^{\mathsf T} V)_e + y^{\mathrm{sh}}_k V_k,$$

the [current injected at bus k](../ac-power-injections-and-network-losses/node-injection.md) into
the network: the signed sum, through $B$, of the branch currents $y_e (B^{\mathsf T} V)_e$, where
$(B^{\mathsf T} V)_e = \sum_v B_{ve} V_v$ is the
[voltage drop](../ac-power-injections-and-network-losses/branch-drop.md) across branch $e$, plus the
shunt current $y^{\mathrm{sh}}_k V_k$.
