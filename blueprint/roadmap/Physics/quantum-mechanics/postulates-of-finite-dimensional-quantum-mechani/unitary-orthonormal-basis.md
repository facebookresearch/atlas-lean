# Unitary Orthonormal Basis

The columns of a unitary matrix `U` as an orthonormal basis of `EuclideanSpace ℂ (Fin n)`:
the `i`-th basis vector is the `i`-th column `U *ᵥ Pi.single i 1`
(`coe_unitaryOrthonormalBasis`). The underlying linear isometry is the `Uᴴ`-action, inverted by
the `U`-action. This is the matrix-to-`OrthonormalBasis` bridge for the canonical
`Quantum.FiniteState` Born API.
