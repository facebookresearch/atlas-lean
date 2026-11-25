# Cyclic Same Side Shortening inr

Cyclic same-side shortening for `Sum.inr` endpoints.

Orientation: word `L = Sum.inr rHead :: middle ++ [Sum.inr rLast]` with
`toStableE (prod L) = 1`. Rotate the last block to the front,
`Lrot = Sum.inr rLast :: Sum.inr rHead :: middle`.

Hypotheses: `n` arbitrary including `0`; `middle` may be `[]`. Shape forces
length ≥ 2; empty and singleton are not inputs.

Conclusions: same five as the `inl` theorem, with `inr` sides and
`length_normalizeBoundaryBlocks_lt_of_adjacent_inr`.

Nonclaims: identical to the `inl` variant.
