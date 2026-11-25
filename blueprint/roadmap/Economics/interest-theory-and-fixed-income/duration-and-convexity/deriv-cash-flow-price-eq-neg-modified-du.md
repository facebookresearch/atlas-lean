# Price derivative is minus modified duration times price

For cash flows `c_t` (any real numbers) paid at the dates `t` of a finite set `s ⊆ ℕ`, let
`P(r) = ∑_{t ∈ s} c_t (1 + r)⁻ᵗ` be the price and `D_mod(r)` the modified duration,
`(∑_{t ∈ s} t c_t (1 + r)⁻ᵗ) / ((1 + r) P(r))`. At every yield `r > -1` with `P(r) ≠ 0`, the
derivative of the price, which exists there, is `P′(r) = -D_mod(r) P(r)`.
