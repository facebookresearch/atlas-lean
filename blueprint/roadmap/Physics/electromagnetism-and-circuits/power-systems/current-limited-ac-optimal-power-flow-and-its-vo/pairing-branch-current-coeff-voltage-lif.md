# On a lift, the branch-current pairing is the squared branch current

For natural numbers $n$ and $m$, every real matrix $B \in \mathbb{R}^{n \times m}$, every
$V \in \mathbb{C}^n$ and $y \in \mathbb{C}^m$, and every branch $e$, the [pairing](pairing.md) of
the [branch-current coefficient matrix](branch-current-coeff.md) $C_e$ with the
[voltage lift](voltage-lift.md) is

$$\langle C_e, V V^{\mathsf H} \rangle = \bigl|y_e\, (B^{\mathsf T} V)_e\bigr|^2,$$

the squared magnitude of the branch current $y_e (B^{\mathsf T} V)_e$, where
$(B^{\mathsf T} V)_e = \sum_v B_{ve} V_v$ is the
[voltage drop](../ac-power-injections-and-network-losses/branch-drop.md) across branch $e$.
