# A voltage vector is AC feasible exactly when its lift is SDP feasible

For every [instance](current-limited-opf.md) of the current-limited optimal power flow problem with
$n$ buses and $m$ branches, with arbitrary data, and every voltage vector $V \in \mathbb{C}^n$: $V$
is [AC feasible](ac-feasible.md) if and only if its [voltage lift](voltage-lift.md)
$V V^{\mathsf H}$ is [feasible for the semidefinite relaxation](sdp-feasible.md). The lift is
positive semidefinite, and at the lift each constraint of the relaxation equals the corresponding AC
constraint: the active and reactive pairings are the [active](pairing-active-coeff-voltage-lift.md)
and [reactive](pairing-reactive-coeff-voltage-lift.md) powers that the buses supply to the network,
the voltage pairings the [squared voltage magnitudes](pairing-voltage-coeff-voltage-lift.md) and the
branch pairings the [squared branch currents](pairing-branch-current-coeff-voltage-lif.md).
