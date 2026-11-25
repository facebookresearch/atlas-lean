# Without self-springs, the stiffness matrix maps the ones vector to w

For a finite set `ι` of nodes, pair weights with `k_{ii} = 0` for every node and wall stiffnesses
`w`, the [stiffness matrix](stiffness-matrix.md) applied to the all-ones vector gives the wall
stiffnesses: `K 1 = w`. No reciprocity of the weights is needed.
