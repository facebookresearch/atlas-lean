# Trail check and exclusive or have the same law

Let `q` be a distribution on `Ω`, `E : Ω → (Fin r → Bool)` the error bits and
`T : Ω → Bool` the trail check, with `T ω` equal to the exclusive or of the
bits `E ω` for every `ω`, and suppose the error bits are independent with laws
`p i` (the pushforward of `q` along `E` is the product distribution of the `p
i`). Then the pushforward of `q` along `T` equals the law of the exclusive or
of `r` independent bits with laws `p i`.
