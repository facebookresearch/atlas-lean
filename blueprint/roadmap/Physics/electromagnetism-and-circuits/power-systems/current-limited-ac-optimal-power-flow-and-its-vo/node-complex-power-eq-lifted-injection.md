# Bus complex power as a linear function of the voltage lift

For natural numbers $n$ and $m$, every real matrix $B \in \mathbb{R}^{n \times m}$, every
$V \in \mathbb{C}^n$, $y \in \mathbb{C}^m$ and $y^{\mathrm{sh}} \in \mathbb{C}^n$, and every bus
$k$, let $Y$ be the [bus admittance matrix](bus-admittance.md) of $B$, $y$ and $y^{\mathrm{sh}}$,
let $I_k = \sum_e B_{ke}\, y_e\, (B^{\mathsf T} V)_e + y^{\mathrm{sh}}_k V_k$ be the
[current leaving bus k into the network](../ac-power-injections-and-network-losses/node-injection.md),
and let $W = V V^{\mathsf H}$ be the [voltage lift](voltage-lift.md). Then

$$V_k\, \overline{I_k} = \sum_{j} \overline{Y_{kj}}\, W_{kj}.$$

The left side is the
[complex power](../ac-power-injections-and-network-losses/node-complex-power.md) that bus $k$
supplies to the network, in the root-mean-square convention $S = V \overline{I}$ without a factor
$1/2$; the right side is the [lifted injection](lifted-injection.md), a linear function of $W$.
Proof: $I_k = (Y V)_k$, so $V_k \overline{I_k} = \sum_j \overline{Y_{kj}}\, V_k \overline{V_j}$.
