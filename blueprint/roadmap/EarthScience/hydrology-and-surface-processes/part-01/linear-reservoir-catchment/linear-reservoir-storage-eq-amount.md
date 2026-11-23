# With nonzero recession, storage equals the one-compartment amount

For a recession coefficient `k ≠ 0` and all real `I`, `S0` and `t`, the linear-reservoir storage
equals the one-compartment amount with elimination rate `k`, constant input `I` and initial amount
`S0`, the variation-of-constants solution of `A' = I - k * A`, `A(0) = S0`:
`I / k + (S0 - I / k) * exp (-k * t) = S0 * exp (-k * t) + ∫₀ᵗ exp (-k * (t - s)) * I ds`, with an
oriented integral when `t < 0`. For `k = 0` the two differ when `I * t ≠ 0`: the storage is `S0`
by the convention `x / 0 = 0`, while the amount is `S0 + I * t`.
