# On a lift, the active pairing equals the active power at the bus

For natural numbers $n$ and $m$, every real matrix $B \in \mathbb{R}^{n \times m}$, every
$V \in \mathbb{C}^n$, $y \in \mathbb{C}^m$ and $y^{\mathrm{sh}} \in \mathbb{C}^n$, and every bus
$k$, let $Y$ be the [bus admittance matrix](bus-admittance.md) of $B$, $y$ and $y^{\mathrm{sh}}$ and
$A^P_k$ its [active coefficient matrix](active-coeff.md) at $k$. Then

$$\langle A^P_k, V V^{\mathsf H} \rangle = \operatorname{Re}\bigl(V_k\, \overline{I_k}\bigr),$$

where $\langle A, W \rangle = \operatorname{Re} \operatorname{tr}(A W)$ is the
[pairing](pairing.md), $V V^{\mathsf H}$ the [voltage lift](voltage-lift.md), and
$I_k = \sum_e B_{ke}\, y_e\, (B^{\mathsf T} V)_e + y^{\mathrm{sh}}_k V_k$ the current leaving bus
$k$ into the network; the right side is the active part of the
[complex power](../ac-power-injections-and-network-losses/node-complex-power.md) that bus $k$
supplies to the network.
