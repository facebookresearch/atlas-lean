# One step of the physical periodic Yee update

For free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, a cell width `h`, a time step
`dt` and grid fields `E, H ∈ ℝᴺ`, the pair `(E_new, H_new)` with `H_new = H − (dt / μ₀) D₋ E` and
then `E_new = E − (dt / ε₀) D₊ H_new`, where `(D₊ w)_j = (w_{j+1} − w_j) / h` and
`(D₋ w)_j = (w_j − w_{j−1}) / h`, indices taken modulo `N` (both `0` when `h = 0`, by the convention
`x / 0 = 0`).
