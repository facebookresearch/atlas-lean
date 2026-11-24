# Sum mul sum map eq sum edge Volume mul

Total travel time on supplied routes, path side equals edge side: with link travel times
`t` fixed at the induced volumes `x = edgeVolume edges f`, the flow-weighted sum of route
travel times `∑ p, f p * ((edges p).map fun e => t e (x e)).sum` equals `∑ e, x e * t e (x e)`.
A route that traverses an arc twice pays its cost twice and loads it twice. Units:
vehicle-flow times time on both sides. With constant `t e _ = c e` this is the identity for
any fixed edge costs `c`.
