# Lifted complex injection at a bus

For a natural number $n$, complex $n \times n$ matrices $Y$ and $W$ and an index $k$, the lifted
injection at $k$ is

$$\sum_{j} \overline{Y_{kj}}\, W_{kj}.$$

It is defined for arbitrary $Y$ and $W$ and is complex-linear in $W$. When $Y$ is the
[bus admittance matrix](bus-admittance.md) of a network and $W = V V^{\mathsf H}$ is the
[voltage lift](voltage-lift.md) of a voltage vector $V$, it equals $V_k \overline{(Y V)_k}$, the
complex power that bus $k$ supplies to the network
([lifted form of the bus power](node-complex-power-eq-lifted-injection.md)).
