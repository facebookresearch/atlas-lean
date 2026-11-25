# Boundary Torus Coord

Per-index coordinate product from a boundary word list: filter by
`Fin n` equality, map `Prod.snd`, take `List.prod`. No `DecidableEq Fˣ`
required; `n = 0` has no coordinate index. No claim about word reconstruction.
