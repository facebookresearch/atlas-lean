# Angular momentum about the centre of mass in body components

Let `M` be a rigid-body motion in three dimensions whose body frame is centred at the centre of
mass (`c = 0`), with orientation `R`, body angular velocity `ω_B` (dual to `Rᵀ Ṙ`) and inertia
tensor `I_B = ∫ (|y|² 1 - y yᵀ) dm` about the centre of mass. At every time `t` at which `R` is
differentiable, the [angular momentum about the centre of mass](com-angular-momentum.md) is
`L_COM(t) = R(t) L_B`, where `L_B = ∫ y × (ω_B(t) × y) dm` is the angular momentum of the body-fixed
distribution turning with angular velocity `ω_B(t)`, and `L_COM(t) = R(t) I_B ω_B(t)`.
