# Map symbol Multilinear

The multilinear symbol is functorial: `MilnorK.map f n` sends
`symbolMultilinear F n v` to `symbolMultilinear K n` with each additive unit
entry transformed by `MilnorKRing.unitsAddHom f`, i.e. `Additive.ofMul`
composed with `Units.map f`.
