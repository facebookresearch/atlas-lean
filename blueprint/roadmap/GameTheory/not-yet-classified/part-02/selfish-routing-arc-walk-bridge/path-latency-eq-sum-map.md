# Path Latency eq sum map

Link-simple bridge for route travel times: on the OD instance with commodity
`p ↦ (orig p, dest p)`, arc sets `(edges p).toFinset` and latency `ℓ`, routes that repeat no
arc give `pathLatency f p = ((edges p).map fun e => ℓ e (edgeVolume edges f e)).sum`, the route
travel time at the induced volumes. Neither side depends on the commodity. `Nodup` is needed:
`pathLatency` charges a repeated arc once, at the set-based `edgeFlow`. With
`cost_eq_sum_pathLatency_mul` and `sum_mul_sum_map_eq_sum_edgeVolume_mul`, the set-based cost
of such routes is the edge-side total travel time.
