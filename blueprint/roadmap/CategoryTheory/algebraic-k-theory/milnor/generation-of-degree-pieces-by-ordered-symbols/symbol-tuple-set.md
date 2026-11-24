# Symbol Tuple Set

The set of tuple symbols of length `n` as elements of `MilnorKRing F`.

This is the `Fin`-indexed counterpart of `symbolListSet`: every tuple symbol
`symbolTuple F n v` coerces to `symbolList F (List.ofFn v)`, and conversely
every list symbol of length `n` arises from a tuple via `ofFn`.
