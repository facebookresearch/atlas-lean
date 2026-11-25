# Linear active-generation cost of a voltage vector

For an [instance](current-limited-opf.md) of the current-limited optimal power flow problem with $n$
buses, cost coefficients $c_k$ and active demands $P^d_k$, and a voltage vector
$V \in \mathbb{C}^n$, the AC cost is

$$\sum_{k} c_k \bigl(\operatorname{Re} S_k + P^d_k\bigr),$$

where $S_k = V_k \overline{I_k}$ is the
[complex power](../ac-power-injections-and-network-losses/node-complex-power.md) that bus $k$
supplies to the network, $I_k$ being the current leaving bus $k$, which
[equals](bus-admittance-mul-vec-eq-node-injection.md) $(Y V)_k$ for the
[bus admittance matrix](admittance.md) $Y$, so that $\operatorname{Re} S_k + P^d_k$ is the active
generation at bus $k$. It is defined for every $V$, feasible or not, and the coefficients $c_k$ may
have any sign.
