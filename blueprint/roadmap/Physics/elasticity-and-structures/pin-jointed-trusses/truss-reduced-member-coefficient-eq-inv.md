# Truss reduced member Coefficient eq inv mul Vec

Truss instance: for the supported compatibility matrix
`axialCompatibility r a b * S` with free coordinates indexed by
the members, square and invertible, member weights
`k` and a supported solution `u`, the separation-form elastic
coefficient vector (axial force divided by member length, the
convention of `supported_virtualWork_iff`) is the reduced
statics solution
`((axialCompatibility r a b * S)ᵀ)⁻¹ *ᵥ f`, and it equilibrates
the supported load in virtual work: internal work
`s ⬝ᵥ ((axialCompatibility r a b * S) *ᵥ v)` equals external
work `f ⬝ᵥ v` for every supported virtual displacement `v`.
The virtual-work conjunct is the canonical
supported virtual-work correspondence.
Reactions at constrained joint coordinates are not addressed:
`f` is the supported load in free coordinates.
