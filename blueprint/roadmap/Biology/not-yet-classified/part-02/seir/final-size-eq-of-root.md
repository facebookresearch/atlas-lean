# The final size is determined by the initial data

Under the hypotheses of
`tendsto_final_size` with `N > 0` and a nonzero infected seed `E(0) + I(0) > 0`, the limit `S∞`
of `S` is the unique root `x ≤ S(0)` of the final-size equation
`x = S(0) e^{-R₀ (S(0) + E(0) + I(0) - x) / N}` (`R₀ = β / γ`). Via
`SIR.final_size_root_unique` with initial infected mass `E(0) + I(0)`.
