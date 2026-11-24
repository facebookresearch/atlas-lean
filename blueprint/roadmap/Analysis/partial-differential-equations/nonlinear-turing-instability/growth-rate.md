# Growth Rate

The **growth rate** of the Fourier mode of wavenumber `k`: the larger root
`λ = (τ + √(τ² - 4 δ)) / 2` of the characteristic polynomial `λ² - τ λ + δ` of the mode matrix
`J - k² D`, where `τ = tr (J - k² D)` and `δ = det (J - k² D)`. When `δ < 0` (which is what an
unstable mode has when `tr J < 0`) it is a positive real eigenvalue of `J - k² D`
(`exists_mulVec_eq_growthRate_smul`, `growthRate_pos`). It is a root whenever `τ² - 4 δ ≥ 0`
(`growthRate_sq_sub`); for a negative discriminant `Real.sqrt` truncates to `0` and the value is
only the common real part `τ / 2`.
