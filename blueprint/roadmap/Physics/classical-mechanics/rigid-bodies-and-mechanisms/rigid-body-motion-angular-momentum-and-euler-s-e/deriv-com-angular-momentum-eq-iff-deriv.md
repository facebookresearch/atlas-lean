# For positive definite inertia, balance gives the angular acceleration

Let `M` be a rigid-body motion in three dimensions whose body frame is centred at the centre of
mass (`c = 0`), with orientation `R`, body angular velocity `ω_B` and symmetric positive definite
inertia tensor `I_B` about the centre of mass, and let `U` be an open set of times on which `R` is
`C²` entry by entry. For every `t ∈ U` and every torque `τ_I ∈ ℝ³` in inertial components,
`dL_COM/dt (t) = τ_I` if and only if `ω_B'(t) = I_B⁻¹ (R(t)ᵀ τ_I - ω_B(t) × (I_B ω_B(t)))`, with
`L_COM` the [angular momentum about the centre of mass](com-angular-momentum.md).
