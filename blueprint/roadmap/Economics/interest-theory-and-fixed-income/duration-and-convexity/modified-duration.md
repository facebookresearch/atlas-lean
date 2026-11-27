# Modified duration of a cash-flow stream

The modified duration at yield `r` of cash flows `c_t` paid at the dates `t` of a finite set
`s ⊆ ℕ` is the Macaulay duration divided by `1 + r`: `D_mod(r) = D_Mac(r) / (1 + r)`, where
`D_Mac(r) = (∑_{t ∈ s} t c_t (1 + r)⁻ᵗ) / ∑_{t ∈ s} c_t (1 + r)⁻ᵗ`. It is defined for every real
`r`, with the convention `x / 0 = 0`: `D_mod(-1) = 0`, and `D_mod(r) = 0` when the price
`∑_{t ∈ s} c_t (1 + r)⁻ᵗ` is `0`.
