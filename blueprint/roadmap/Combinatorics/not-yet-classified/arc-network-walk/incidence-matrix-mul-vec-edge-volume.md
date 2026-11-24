# Incidence Matrix mul Vec edge Volume

Node balance of the edge volumes, route by route: if every supplied route is a valid walk
from its origin to its destination, inflow minus outflow of the edge volumes at `v` is the
flow on routes ending at `v` minus the flow on routes starting at `v`. No sign or demand
condition on `f` is used. The per-route identity is the arc-list form of the telescoping
`MathlibExt.Probability.CanonicalPaths.sum_pathEdges_sub`.
