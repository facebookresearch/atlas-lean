# Trail correlation is the product of correlations

Let `q` be a distribution on `Ω`, `E : Ω → (Fin r → Bool)` the error bits and
`T : Ω → Bool` the trail check, with `T ω` equal to the exclusive or of the
bits `E ω` for every `ω`, and suppose the error bits are independent with laws
`p i` (the pushforward of `q` along `E` is the product distribution of the `p
i`). Then the correlation `Pr[false] - Pr[true]` of the trail check is the
product of the correlations of the `p i`, for every `r`.
