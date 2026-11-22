# Ideal Gas P

Ideal-gas pressure `p = n * R * T / V` of `n` moles at temperature `T` in volume `V` (model
assumption: the ideal-gas equation of state). Physical states have `V > 0`; at `V = 0` Lean's
convention `x / 0 = 0` gives the meaningless value `0`, and the results below use `idealGasP`
only for `V > 0`.
