# Edge Flow eq edge Volume

Link-simple bridge to the set-based routing model: on the OD instance with commodity
`p ↦ (orig p, dest p)`, arc sets `(edges p).toFinset` and any latency `ℓ`, routes that repeat
no arc give `edgeFlow f e = edgeVolume edges f e`. Neither side depends on the commodity or
the latency. `Nodup` is needed: `edgeFlow` counts a repeated arc once.
