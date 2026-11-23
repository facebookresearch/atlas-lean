# Critical Coverage

The **critical vaccination coverage** `p_c = (1 - 1 / R₀) / ε = (1 - γ / β) / ε`. It has its
epidemiological meaning for `β, ε > 0`; Lean's convention `x / 0 = 0` makes it `0` at `ε = 0` and
`1 / ε` at `β = 0`, and the threshold theorems (`Rv_lt_one_iff` and its variants) assume
`β, γ, ε > 0`.
