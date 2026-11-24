# Incidence transfer of the aggregate turning flows

Let `E` (links) and `C` (commodities) be finite types and `q(c, e, e')` a turning certificate. On
the turning-movement network, whose nodes are the links and whose arcs are the ordered link pairs
`(e, e')` (from `e` to `e'`), apply the incidence matrix, `B(v, m) = 1` if the arc `m` ends at `v`,
`-1` if it starts at `v` (`0` for a loop) and `0` otherwise, to the aggregate turning flows
`m ↦ ∑_c q(c, m)`. At every link `e` the result is the aggregate upstream boundary flow of `e` minus
its aggregate downstream boundary flow, `∑_c ∑_{e₀} q(c, e₀, e) - ∑_c ∑_{e'} q(c, e, e')`: inflow
minus outflow.
