# Anode-to-cathode current of a diode branch from the node potentials

Let a [diode occupy branch](diode-branch.md) $e$ with anode $a$ and cathode $c$, $a \ne c$, for
any real parameters $I_s, n, k_B, T, q$, and let the branch voltages come from node potentials
$\phi$: $v$ is the transposed [electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)
applied to $\phi$, so that
[$v_e = \phi(\text{tail}(e)) - \phi(\text{head}(e))$](../../circuit-theory/tellegen-s-theorem-and-branch-power-balance/branch-voltage-eq-tail-sub-head.md).
Then the physical anode-to-cathode current $s\, i_e$, with $s = \pm 1$ the orientation sign of the
anode, is the [diode current](diode-current.md) at the anode-to-cathode potential difference:

$$s\, i_e = I_D(\phi(a) - \phi(c)),$$

whichever way the branch is oriented.
