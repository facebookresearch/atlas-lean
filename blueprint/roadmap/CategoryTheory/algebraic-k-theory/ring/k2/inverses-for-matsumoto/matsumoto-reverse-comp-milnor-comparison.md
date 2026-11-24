# Matsumoto Reverse comp milnor Comparison eq id

Conditional Milnor-side inverse: if `matsumotoReverse` agrees with
`MilnorK.k2Symbol` on every algebraic Steinberg symbol, then its composite
with `milnorComparison` is the identity on `MilnorK F 2` as a `ℤ`-linear map.

This is stated as equality of `ℤ`-linear maps via `toIntLinearMap`,
so `k2Symbol_ext` applies directly and the bridge theorem can discharge `h`.
