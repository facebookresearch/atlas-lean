# The branch drop through the electrical incidence is tail minus head

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For complex
node voltages `V_v`, the
[branch voltage drop](../ac-power-injections-and-network-losses/branch-drop.md) through the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)
is `d_e = V_{t(e)} - V_{h(e)}` for every branch `e`; for a loop, `t(e) = h(e)`, it is `0`.
