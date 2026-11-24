# Supported unit Load identity

Unit-load identity: for one supported stiffness with positive
member weights and positive-definite certificate, a supported
solution `K *ᵥ u = f` with separation-form coefficient vectors
`N = Matrix.diagonal k *ᵥ ((B S) *ᵥ u)` and
`n = Matrix.diagonal k *ᵥ ((B S) *ᵥ (K⁻¹ *ᵥ aout))` (axial force
divided by member length) satisfies
`aout ⬝ᵥ u = n ⬝ᵥ (D⁻¹ *ᵥ N)`, where `D⁻¹` is the pointwise inverse
diagonal `Matrix.diagonal (fun e => (k e)⁻¹)` (generalized
compliances for the separation-form weights — for physical weights
`EA / L ^ 3` this is `L ^ 3 / EA`, not member flexibility
`L / EA`; the physical axial-force form is
`supported_unitLoad_axialForce_identity` below). The separation form
is the preceding identity; the two member pairings agree through
recovery of `(B S) *ᵥ u` from `N`, which is where positivity of the
weights enters. Both load cases share the one stiffness, supports
and reference configuration.
