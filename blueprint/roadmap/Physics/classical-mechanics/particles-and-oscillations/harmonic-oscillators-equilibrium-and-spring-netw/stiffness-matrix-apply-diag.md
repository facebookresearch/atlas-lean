# Diagonal entries of the stiffness matrix

For a finite set `ι` of nodes, pair weights `k` and wall stiffnesses `w`, the diagonal entries of
the [stiffness matrix](stiffness-matrix.md) are `K_{ii} = (∑_{l ∈ ι} k_{il}) + w_i` for every node
`i` (the sum includes `k_{ii}`).
