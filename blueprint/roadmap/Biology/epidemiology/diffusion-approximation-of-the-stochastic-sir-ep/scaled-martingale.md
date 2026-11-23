# Scaled Martingale

The scaled martingale `M_N(t) = √N (X_N(t) - X_N(0) - ∫₀ᵗ F(X_N(s)) ds)`. For the SIR chain
in its random time-change representation this is
`Σ_ℓ ℓ N^{-1/2} (Y_ℓ(N ∫₀ᵗ λ_ℓ(X_N)) - N ∫₀ᵗ λ_ℓ(X_N))` with unit Poisson processes `Y_ℓ`. For a
general family `X` it is just the process above: it is a martingale only when `X` is the scaled
SIR chain, and no result here uses the martingale property.
