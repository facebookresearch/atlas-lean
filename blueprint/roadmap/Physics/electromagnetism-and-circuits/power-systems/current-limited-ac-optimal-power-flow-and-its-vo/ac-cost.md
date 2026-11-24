# Linear active-generation cost of a voltage vector

For an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with $n$
buses, cost coefficients $c_k$ and active demands $P^d_k$, and a voltage vector
$V \in \mathbb{C}^n$, the AC cost is

$$\sum_{k} c_k \bigl(\operatorname{Re} S_k + P^d_k\bigr),$$

where $S_k = V_k \overline{(Y V)_k}$ is the
[complex power](../ac-power-injections-and-network-losses/node-complex-power.md) that bus $k$
supplies to the network, $Y$ being the [bus admittance matrix](admittance.md), so that
$\operatorname{Re} S_k + P^d_k$ is the active generation at bus $k$. It is defined for every $V$,
feasible or not, and the coefficients $c_k$ may have any sign.
