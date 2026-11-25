# For reciprocal weights without self-springs, energy is half of uᵀKu

Let `ι` be a finite set of nodes, with pair weights `k` satisfying `k_{ij} = k_{ji}` and
`k_{ii} = 0` for all nodes, wall stiffnesses `w` and displacements `u : ι → ℝ`. Then the
[spring energy](spring-energy.md) is half the quadratic form of the
[stiffness matrix](stiffness-matrix.md) `K`:

`U(k, w, u) = (1/2) uᵀ K u`.
