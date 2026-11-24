# Physical-to-canonical bridge

On the turning-movement network, whose nodes are links and
whose arcs are ordered link pairs, the canonical incidence transfer of the aggregate turning
flows at link `e` is the aggregate upstream boundary flow of `e` minus its aggregate downstream
boundary flow. So over a step of length `dt` the junction transfer changes link vehicle
counts by `dt` times this canonical incidence transfer, in addition to the external source
and sink faces, in the inflow-minus-outflow sign of `incidenceMatrix`.
