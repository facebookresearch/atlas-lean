# Unserved of not reachable

Unreachable OD pairs are unserved: if every supplied route is a valid walk and `d` is not
reachable from `o` along arcs (tail to head), then no supplied route has OD pair `(o, d)`, so
so the admission results `RoutingInstance.exists_isFeasible_iff` and
`RoutingInstance.not_exists_sum_eq_of_forall_commodity_ne` at the commodity map
`p ↦ (orig p, dest p)` apply to `(o, d)`.
