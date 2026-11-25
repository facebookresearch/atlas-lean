# The angular momentum balance law is equivalent to Euler's equations

Let `M` be a rigid-body motion in three dimensions whose body frame is centred at the centre of
mass (`c = 0`), with orientation `R`, body angular velocity `ω_B` and inertia tensor `I_B` about the
centre of mass, and let `U` be an open set of times on which `R` is `C²` entry by entry. For every
`t ∈ U` and every torque `τ_I ∈ ℝ³` in inertial components, `dL_COM/dt (t) = τ_I` if and only if
Euler's equations `I_B ω_B' + ω_B × (I_B ω_B) = Rᵀ τ_I` hold at `t`, with `L_COM` the
[angular momentum about the centre of mass](com-angular-momentum.md) and `Rᵀ τ_I` the
[body components](../body-fixed-and-inertial-frames/inertial-to-body-vec.md) of the torque.
