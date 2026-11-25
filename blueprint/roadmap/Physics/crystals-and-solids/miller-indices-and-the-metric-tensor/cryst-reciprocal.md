# Crystallographic reciprocal basis without the factor 2π

For a [Bravais lattice](../bravais-lattices/bravais-lattice.md) with basis matrix `B` and
`j ∈ {0, 1, 2}`, the crystallographic reciprocal basis vector `b_j` is the `j`-th column of
`(B⁻¹)ᵀ`, with no factor `2π`. It satisfies `a_i · b_j = δ_ij`
([duality](inner-cryst-reciprocal-primitive-vector.md)); the physics-convention reciprocal lattice
carries the factor `2π` ([relation](reciprocal-vector-eq-phys-smul.md)).
