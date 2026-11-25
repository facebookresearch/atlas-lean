# The relaxation cost of a lift equals the AC cost

For every [instance](current-limited-opf.md) of the current-limited optimal power flow problem with
$n$ buses and every $V \in \mathbb{C}^n$, feasible or not, the [relaxation cost](sdp-cost.md) of the
[voltage lift](voltage-lift.md) $V V^{\mathsf H}$ equals the [AC cost](ac-cost.md) of $V$:

$$\sum_{k} c_k \bigl(\langle A^P_k, V V^{\mathsf H} \rangle + P^d_k\bigr) =
\sum_{k} c_k \bigl(\operatorname{Re} S_k + P^d_k\bigr),$$

where $A^P_k$ is the [active coefficient matrix](active-coeff.md) of the bus admittance matrix at
bus $k$ and $S_k$ the complex power that bus $k$ supplies to the network.
