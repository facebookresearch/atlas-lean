# Fourier Coeff

The sine coefficients `bₙ = 2c₀ (1 - (-1)ⁿ) / (nπ)` of the uniform initial profile `c₀` on
`[0, L]`, with `b₀ = 0`: `4c₀ / (nπ)` for odd `n` and `0` for even `n`. They do not depend on the
width `L`, which is a parameter only so that `fourierCoeff c₀ L` and `fourierTerm c₀ L D` take the
same arguments. `fourierCoeff_formula` identifies them with `(2/L) ∫₀ᴸ c₀ sin(nπx/L) dx` for
`L > 0` and `n ≥ 1`.
