# Kappa Max

The **maximum kappa for the margins of `P`**:
`κ_max = (∑ᵢ min(pᵢ., p.ᵢ) - p_e) / (1 - p_e)`. It is the maximum of `κ` over the joint
probability tables with the margins of `P` when `P` is a joint probability table with
`p_e < 1` (`kappa_le_kappaMax`). At `p_e = 1` the denominator vanishes, and the formula gives `0`
by the convention `x / 0 = 0`.
