# AC feasibility of a voltage vector

Let an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with $n$
buses and $m$ branches be given, with incidence matrix $B$, branch admittances $y$ and shunt
admittances $y^{\mathrm{sh}}$, and let $V \in \mathbb{C}^n$ be a vector of complex node voltages
(root-mean-square phasors). Write $(B^{\mathsf T} V)_e = \sum_v B_{ve} V_v$ for the
[voltage drop](../ac-power-injections-and-network-losses/branch-drop.md) across branch $e$,
$y_e (B^{\mathsf T} V)_e$ for the branch current,

$$I_k = \sum_{e} B_{ke}\, y_e\, (B^{\mathsf T} V)_e + y^{\mathrm{sh}}_k V_k$$

for the
[current leaving bus k into the network](../ac-power-injections-and-network-losses/node-injection.md),
which [equals](bus-admittance-mul-vec-eq-node-injection.md) $(Y V)_k$ for the
[bus admittance matrix](admittance.md) $Y$, and $S_k = V_k \overline{I_k}$ for the
[complex power](../ac-power-injections-and-network-losses/node-complex-power.md) that bus $k$
supplies to the network (no factor $1/2$). The vector $V$ is AC feasible if

- $P^{\min}_k \le \operatorname{Re} S_k + P^d_k \le P^{\max}_k$ for every bus $k$;
- $Q^{\min}_k \le \operatorname{Im} S_k + Q^d_k \le Q^{\max}_k$ for every bus $k$;
- $v^{\min}_k \le |V_k|^2 \le v^{\max}_k$ for every bus $k$;
- $|y_e (B^{\mathsf T} V)_e|^2 \le i^{\max}_e$ for every branch $e$.

The generation at bus $k$ is the power it supplies to the network plus its demand, so its active and
reactive parts are $\operatorname{Re} S_k + P^d_k$ and $\operatorname{Im} S_k + Q^d_k$. Line limits
bound only the squared current magnitudes; apparent-power and phase-angle limits are not part of the
problem. No ordering or sign of the data is assumed.
