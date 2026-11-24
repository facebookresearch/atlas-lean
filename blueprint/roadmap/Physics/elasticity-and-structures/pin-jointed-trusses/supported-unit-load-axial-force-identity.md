# Supported unit Load axial Force identity

Unit-load identity in physical axial forces: under the
`supported_unitLoad_identity` data with noncoincident endpoints,
rescaling the separation-form coefficients by member length
(`N e * L e` is the physical axial force, tension positive) gives
`aout ⬝ᵥ u = ∑ e, nphys e * (Nphys e / (k e * (L e) ^ 2))`; for
physical separation-form weights `k e = EA / (L e) ^ 3` the
denominator `k e * (L e) ^ 2` is `EA / L e`, the classical
dummy-unit-load sum `∑ n N L / EA`.
