# The lower endpoint load attains the lower envelope

Let `ι` be a finite set of load coordinates, `η` a fixed influence vector and `cap` a vector of
pattern capacities, both indexed by `ι`, with `cap_i ≥ 0` for all `i`. The
[lower endpoint load](lower-box-load.md) `f` lies in the box, `0 ≤ f_i ≤ cap_i` for all `i`, and its
response `η · f` equals the lower envelope value `∑_i cap_i * min(η_i, 0)`, so the
[lower envelope bound](box-lower-le-dot-product.md) is attained. The nonnegativity of the capacities
makes the endpoint load feasible.
