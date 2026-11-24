# Exists rayleigh modal decoupling

Physical-to-canonical bridge: for a positive-definite mass `M`, a positive-semidefinite
stiffness `K` and Rayleigh coefficients `α, β ≥ 0`, the canonical modal-basis
theorem (`PhyslibExt.Mechanics.ModalResponse.exists_modalBasis`) yields an invertible
mass-orthonormal basis `Φ` with `Φᵀ * K * Φ = diagonal μ`, nonnegative `μ j` and
nonnegative modal damping `α + β * μ j`, in which every trajectory and load decouple as in
`rayleigh_modal_decoupling`. Repeated eigenvalues and rigid modes (`μ j = 0`) included.
