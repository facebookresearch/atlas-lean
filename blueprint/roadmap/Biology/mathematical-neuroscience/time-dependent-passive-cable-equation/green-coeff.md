# Green Coeff

Cosine coefficients `1 / L` for the uniform mode and `(2 / L) cos (n π x₀ / L)` for `n ≥ 1`.
For `0 < L` and `x₀ ∈ [0, L]` these are the coefficients of a unit point charge at `x₀` on the
sealed cable `[0, L]`: the pairings `cos (n π x₀ / L)` of `δ_{x₀}` with the modes, divided by the
self-inner-products `L` and `L / 2`. The formula is used for every real `x₀` and `L`; it is even
and `2L`-periodic in `x₀` (`greenCoeff_neg_source`, `greenCoeff_add_two_mul_source`), so it does
not single out a source outside `[0, L]` from its image inside. They are bounded
(`abs_greenCoeff_le`), and for `L ≠ 0` not summable (at `L = 0` division by zero makes every
coefficient `0`).
