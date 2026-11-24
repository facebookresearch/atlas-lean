# Applied to branch currents the incidence matrix gives net outflow

For all maps `tail, head` from finitely many branches to finitely many nodes, every vector `i` of
branch currents and every node `v`, the [tail-positive incidence matrix](physical-incidence.md) `B`
satisfies `(B i)(v) = ∑_{e : tail(e) = v} i_e - ∑_{e : head(e) = v} i_e`: the current leaving `v`
minus the current entering `v`.
