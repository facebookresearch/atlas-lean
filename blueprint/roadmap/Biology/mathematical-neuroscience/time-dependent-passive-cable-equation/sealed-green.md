# Green's function of the sealed cable

The cosine series
`G(t, x; x₀) = e^{-t/τ} / L + (2 / L) ∑_{n ≥ 1} e^{-k_n t} cos (n π x₀ / L) cos (n π x / L)`.
For `0 < L` and `x₀ ∈ [0, L]` it is the potential at position `x` and time `t` after a unit
charge is injected at `x₀` at time `0` (an instantaneous, spatially localized synaptic input).
The definition and the theorems about it accept every real `x₀` and (where needed) every
`L ≠ 0`; for other values it is an algebraic extension, not a point charge at `x₀`: it is even
and `2L`-periodic in `x₀` (`sealedGreen_neg_source`, `sealedGreen_add_two_mul_source`), so a
source outside `[0, L]` is its reflected image inside, and replacing `L` by `-L` negates it
(`sealedGreen_neg_length`).
