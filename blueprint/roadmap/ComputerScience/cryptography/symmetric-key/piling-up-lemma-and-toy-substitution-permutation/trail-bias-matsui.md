# Trail bias in Matsui form

Let `q` be a distribution on `Ω`, `E : Ω → (Fin r → Bool)` the error bits and
`T : Ω → Bool` the trail check, with `T ω` equal to the exclusive or of the
bits `E ω` for every `ω`, and suppose the error bits are independent with laws
`p i` (the pushforward of `q` along `E` is the product distribution of the `p
i`). If `bias (p i) = eps i` for every `i` and `1 ≤ r`, the trail check is
`false` with probability `1/2 + 2 ^ (r - 1) * ∏ i, eps i`. The independence of
the error bits is a hypothesis, not a consequence of key independence.
