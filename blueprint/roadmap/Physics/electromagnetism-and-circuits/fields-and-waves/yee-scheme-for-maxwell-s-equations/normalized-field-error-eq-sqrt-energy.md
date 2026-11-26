# The normalized error is the square root of twice the error energy

For free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, `E_y, H_z : ℝ² → ℝ`, all reals
`h` and `dt`, initial grid fields `E0, H0 ∈ ℝᴺ` and every `n`, the
[normalized error](normalized-field-error.md) at step `n` equals `√(2 W_n)`, where `W_n` is the
[discrete energy](grid-field-energy.md) of the error fields `U_n − Eⁿ` and `V_n − Hⁿ` (staggered
samples minus the `n`-th [physical Yee iterate](physical-yee-iterate.md)).
