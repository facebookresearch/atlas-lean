# Total branch power equals the power supplied at the nodes

Let `B` be any real matrix with `n_N` rows (nodes) and `n_B` columns (branches), `φ` and `j` real
node potentials and node injections, and `v` and `i` real branch voltages and currents, with
`v = Bᵀ φ` and `B i = j`. Then the total absorbed branch power equals the supplied node power:

`v · i = φ · j`.

This is the case of numbered nodes and branches of
[Tellegen's theorem in matrix form](../tellegen-s-theorem-and-branch-power-balance/branch-power-eq-node-power.md).
