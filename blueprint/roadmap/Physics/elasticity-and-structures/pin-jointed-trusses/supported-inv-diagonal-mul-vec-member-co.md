# Supported inv Diagonal mul Vec member Coefficient

The pointwise inverse diagonal recovers the separation-form
pairing vector from the elastic coefficient vector: for positive
member weights `k`, applying `Matrix.diagonal (fun e => (k e)⁻¹)` to
the coefficient vector `Matrix.diagonal k *ᵥ ((B S) *ᵥ u)` returns
`(B S) *ᵥ u`, whose entries are member length times elongation (the
coefficients are axial force divided by member length, as at
`supported_virtualWork_iff`). The inverses are scalar inverses
`(k e)⁻¹` (generalized compliances for the separation-form weights);
positivity is used as nonvanishing member by member. No stiffness
inverse occurs.
