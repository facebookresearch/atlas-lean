# Two-bus example: a feasible voltage whose lift has the same cost 1/4

For the [two-bus instance](two-bus-example.md), the voltage vector $V = (1, 1/2)$ is
[AC feasible](ac-feasible.md), its [voltage lift](voltage-lift.md) $V V^{\mathsf H}$ is
[feasible for the semidefinite relaxation](sdp-feasible.md), and both the [AC cost](ac-cost.md) of
$V$ and the [relaxation cost](sdp-cost.md) of $V V^{\mathsf H}$ equal $1/4$. Here the nodal currents
are $Y V = (1/2, -1/2)$, the complex powers that the buses supply to the network are
$S = (1/2, -1/4)$, the squared voltage magnitudes are $1$ and $1/4$, and the squared branch current
is $1/4$. Since $V \ne 0$, the lift has rank one.
