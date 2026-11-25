# Observed intensity is affine in the source coefficients

Let the absorption coefficient `κ` be continuous, let `s` be a finite set of indices with
continuous basis functions `bᵢ` and real coefficients `aᵢ` for `i ∈ s`, and let the intensity
`I` be differentiable at every real `t` with `I'(t) = -κ(t) I(t) + ∑ᵢ aᵢ bᵢ(t)` and
`I(0) = I0`. Then for every `L ≥ 0`, `I(L) = I0 exp(-∫₀ᴸ κ(x) dx) + ∑ᵢ aᵢ wᵢ`, with weights
`wᵢ = ∫₀ᴸ bᵢ(t) exp(-∫ₜᴸ κ(x) dx) dt` that do not depend on the coefficients.
