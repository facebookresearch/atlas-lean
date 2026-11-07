# Solution of Henderson's mixed-model equations

`(β, g)` solves Henderson's mixed-model equations with `R = σ_e² I` and `G = σ_g² K`,
i.e. the specialization of `MixedModel.IsMMESolution` to `Z = 1` (every individual has its
own genetic effect), `G = σ_g² K`, `R = σ_e² I`. In unfolded form this is
`Xᵀ R⁻¹ X β + Xᵀ R⁻¹ g = Xᵀ R⁻¹ y` and `R⁻¹ X β + (R⁻¹ + G⁻¹) g = R⁻¹ y`. The equations
are meaningful when `G` is invertible (`isMMESolution_iff`); otherwise `G⁻¹` is Lean's
junk inverse `0`.
