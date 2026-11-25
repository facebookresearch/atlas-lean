# Without self-springs, a wall-fixed node rules out the rigid zero mode

For a finite set `ι` of nodes, pair weights with `k_{ii} = 0` for every node, wall stiffnesses `w`
and a node `i` with `w_i > 0`, the `i`-th entry of the [stiffness matrix](stiffness-matrix.md)
applied to the all-ones vector is nonzero, `(K 1)_i ≠ 0`; it equals `w_i`. So the all-ones vector
is not in the kernel of `K`.
