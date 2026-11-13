# Martingale difference arrays satisfy Aldous's condition

Let row `n` of `ξ` be a
square-integrable martingale difference sequence for `𝓕 n` (`ξ n i` is `𝓕 n (i+1)`-measurable,
`E[ξ n i | 𝓕 n i] = 0`). If the predictable quadratic variation at each time converges in
probability to the identity, `∑_{j < ⌊n t⌋} E[ξ n j² | 𝓕 n j] → t` for every `t ∈ [0,1]`, then
the partial sums satisfy `AldousCondition`.

## Sources

- Jacod–Shiryaev (2003), Theorem VI.4.13 (Rebolledo's criterion: tightness of the predictable quadratic variations implies Aldous's condition for locally square-integrable martingales), via Lenglart's inequality; here the limit of the quadratic variation is the continuous deterministic function `t`, and pointwise convergence upgrades to uniform control over windows because the quadratic variation is nondecreasing (`sub_le_of_grid`).
