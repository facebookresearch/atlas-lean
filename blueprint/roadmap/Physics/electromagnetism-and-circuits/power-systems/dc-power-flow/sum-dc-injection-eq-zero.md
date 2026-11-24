# The DC injections sum to zero

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For all real
branch susceptances `b_e` and node phase angles `θ_v`, the [DC nodal injections](dc-injection.md)
sum to zero over all nodes:

`∑_v p_v = 0`.

Balance is a consequence of the model, not a hypothesis: every column of the
[electrical incidence](../../circuit-theory/tellegen-s-theorem-and-branch-power-balance/electrical-incidence.md)
sums to zero. In particular, the injection at any node, the reference node included, is minus the
sum of the injections at the other nodes. In the physical reading the susceptances are positive; the
identity holds for all real `b`.
