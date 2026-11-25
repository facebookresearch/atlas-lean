# Macaulay duration of a cash-flow stream

The Macaulay duration at yield `r` of cash flows `c_t` paid at the dates `t` of a finite set
`s ⊆ ℕ` is `D_Mac(r) = (∑_{t ∈ s} t c_t (1 + r)⁻ᵗ) / P(r)`, where
`P(r) = ∑_{t ∈ s} c_t (1 + r)⁻ᵗ` is the price; for positive cash flows and `r > -1` it is the
average of the payment dates weighted by the present values of the payments. It is defined for
every real `r`, with the conventions `x / 0 = 0` (so `D_Mac(r) = 0` when `P(r) = 0`) and
`0⁻¹ = 0` at `r = -1`.
