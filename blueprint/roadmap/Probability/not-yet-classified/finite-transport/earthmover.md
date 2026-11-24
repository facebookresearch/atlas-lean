# Earthmover

Earthmover (optimal-transport) value between two probability
distributions: the infimum of transport costs over all couplings. The
ground cost `d` is unconstrained, so for signed costs this value can be
negative and is not in general a distance; it is the earthmover
distance when `d` is a metric. The marginals range over the subtype of
probability vectors, so a coupling always exists (`exists_coupling`)
and the infimum is over a nonempty index set.
