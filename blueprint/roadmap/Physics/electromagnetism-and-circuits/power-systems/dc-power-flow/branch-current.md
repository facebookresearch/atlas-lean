# Branch current from an admittance and a voltage drop

For a real `n_N × n_E` matrix `B`, complex node voltages `V_v` and complex branch admittances `y_e`,
the current of branch `e` is

`I_e = y_e d_e`, where `d_e = ∑_v B_{ve} V_v`

is the [branch voltage drop](../ac-power-injections-and-network-losses/branch-drop.md); `B_{ve} I_e`
is the term of branch `e` in the
[current injected at node](../ac-power-injections-and-network-losses/node-injection.md) `v`. When
`B` is the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)
of a network whose branch `e` runs from `t(e)` to `h(e)`,
[`d_e = V_{t(e)} - V_{h(e)}`](branch-drop-electrical-incidence.md) and `I_e` is the current flowing
through `e` from its tail to its head.
