# Independent identically distributed offspring numbers

For a measure `P` on a measurable space `Ω` and a measure `ν` on `ℕ`, random offspring numbers
`ξ_n(i) : Ω → ℕ` (the `i`-th individual of generation `n`) form an offspring family with law `ν` if
every `ξ_n(i)` is measurable, the family `(ξ_n(i))_{(n, i)}` is independent under `P`, and the image
measure of `P` under every `ξ_n(i)` is `ν`. When `ν` is a probability measure,
[so is `P`](is-probability-measure.md). No probability measure is assumed, but the independence
condition forces both: for the empty subfamily it says `P(Ω) = 1`, and then `ν(ℕ) = P(Ω) = 1`.
