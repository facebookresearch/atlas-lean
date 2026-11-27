# Earthmover value

For probability distributions `S` and `T` on a finite type `V`
(nonnegative entries summing to `1`) and a ground cost `d : V → V → ℝ`, the earthmover
(optimal-transport) value is the infimum of `transportCost d π` over all couplings `π` of
`S` and `T`. The marginals range over the subtype of probability vectors, so a coupling
always exists (`isCoupling_mul`) and the infimum is over a nonempty index set. The ground
cost is unconstrained, so for signed costs the value can be negative and is not in general
a distance; it is the earthmover distance when `d` is a metric.
