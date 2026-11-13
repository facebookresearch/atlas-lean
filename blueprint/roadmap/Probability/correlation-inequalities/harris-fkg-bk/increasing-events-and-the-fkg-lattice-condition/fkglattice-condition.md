# FKG lattice condition

The *FKG lattice condition* on a weight `π : ConfigSpace E → ℝ`:
`π ω * π ω' ≤ π (ω ⊔ ω') * π (ω ⊓ ω')` for all configurations `ω ω'`. For a positive weight this
is log-supermodularity. Mathlib's `fkg` and `holley` state it in the form
`π a * π b ≤ π (a ⊓ b) * π (a ⊔ b)`.
